import Mathlib
import RHLean.Proof.TerminalAxiomAudit
import RHLean.Analysis.PrimeDilateCofactorPrimeWindows
import RHLean.Proof.TerminalMertensReduction

/-!
# First-jump residual as a low-cofactor prime-window pairing

PR #570 identifies the tail-empty first-jump residual with a literal high-prime
Mertens band.  The generic prime-dilate shell identity already in the repository
removes each lower-scale Mertens value before any norm is taken.  This module
specializes that identity to the first-jump band.

For one fixed prime-dilate coordinate `p`, the band on `(sqrt R, K]` becomes a
signed sum over cofactors.  Cofactors above `sqrt R` contribute exactly zero, so
the support contracts to the fourth-root side before the endpoint difference is
formed.  The resulting prime-window support embeds into the existing canonical
rough-prime partner carrier at root `sqrt R + 1`; it is a windowed subcarrier,
not a new covariance object.

No absolute value, PNT estimate, prime-gap input, RH hypothesis, or new axiom is
introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Zero-extended cofactor response of the high-prime band `(sqrt R, K]` at
endpoint `X`.  The two prime counts have the same multiplicative upper wall and
differ only by the prime cutoff. -/
def firstJumpHighPrimeCofactorResponse
    (p R K X c : ℕ) : ℂ :=
  if c ∈ primeDilateCofactorSupport p X then
    primeDilateCofactorWindowPrimeCount p (Nat.sqrt R) X c -
      primeDilateCofactorWindowPrimeCount p K X c
  else
    0

/-- Physical cofactor carrier after the square-root support contraction. -/
def firstJumpHighPrimeCofactorSupport
    (p R X : ℕ) : Finset ℕ :=
  primeDilateCofactorSupport p X ∩ Finset.Icc 1 (Nat.sqrt R)

/-- Every retained cofactor is on the low side of the square-root cut. -/
theorem firstJumpHighPrimeCofactorSupport_le_sqrt
    {p R X c : ℕ}
    (hc : c ∈ firstJumpHighPrimeCofactorSupport p R X) :
    c ≤ Nat.sqrt R := by
  exact (Finset.mem_Icc.mp (Finset.mem_inter.mp hc).2).2

/-- The common low-cofactor carrier is monotone in the physical endpoint. -/
theorem firstJumpHighPrimeCofactorSupport_mono
    {p R A B : ℕ} (hAB : A ≤ B) :
    firstJumpHighPrimeCofactorSupport p R A ⊆
      firstJumpHighPrimeCofactorSupport p R B := by
  intro c hc
  rcases Finset.mem_inter.mp hc with ⟨hcA, hcRoot⟩
  rcases mem_primeDilateCofactorSupport.mp hcA with
    ⟨hc1, hcA', hfree⟩
  exact Finset.mem_inter.mpr
    ⟨mem_primeDilateCofactorSupport.mpr
      ⟨hc1, hcA'.trans hAB, hfree⟩,
      hcRoot⟩

/-- If a cofactor lies strictly above `sqrt R`, every prime-dilate window whose
prime cutoff is at least `sqrt R` is empty at every endpoint `X <= R`. -/
theorem primeDilateCofactorWindowPrimeCount_eq_zero_of_sqrt_lt_cofactor
    {p R X y c : ℕ}
    (hXR : X ≤ R) (hcs : Nat.sqrt R < c)
    (hsy : Nat.sqrt R ≤ y) :
    primeDilateCofactorWindowPrimeCount p y X c = 0 := by
  have hcpos : 0 < c := by omega
  have hclock : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hsc : Nat.sqrt R + 1 ≤ c := by omega
  have hmul :
      (Nat.sqrt R + 1) ^ 2 ≤ (Nat.sqrt R + 1) * c := by
    simpa [pow_two] using
      Nat.mul_le_mul_left (Nat.sqrt R + 1) hsc
  have hXlt : X < (Nat.sqrt R + 1) * c :=
    hXR.trans_lt (hclock.trans_le hmul)
  have hdivlt : X / c < Nat.sqrt R + 1 :=
    (Nat.div_lt_iff_lt_mul hcpos).2 hXlt
  have hupper : X / c ≤ Nat.sqrt R := by omega
  have hle :
      primeDilateCofactorWindowUpper X c ≤
        primeDilateCofactorWindowLower p y X c := by
    unfold primeDilateCofactorWindowUpper primeDilateCofactorWindowLower
    exact hupper.trans (hsy.trans (le_max_left _ _))
  unfold primeDilateCofactorWindowPrimeCount primeDilateCofactorWindow
  rw [Finset.Ioc_eq_empty_of_le hle]
  simp

/-- Consequently the whole high-prime cofactor response vanishes above the
square-root cofactor support. -/
theorem firstJumpHighPrimeCofactorResponse_eq_zero_of_sqrt_lt_cofactor
    {p R K X c : ℕ}
    (hXR : X ≤ R) (hsK : Nat.sqrt R ≤ K)
    (hcs : Nat.sqrt R < c) :
    firstJumpHighPrimeCofactorResponse p R K X c = 0 := by
  unfold firstJumpHighPrimeCofactorResponse
  by_cases hc : c ∈ primeDilateCofactorSupport p X
  · simp only [hc, if_true]
    rw [primeDilateCofactorWindowPrimeCount_eq_zero_of_sqrt_lt_cofactor
      hXR hcs (le_refl _),
      primeDilateCofactorWindowPrimeCount_eq_zero_of_sqrt_lt_cofactor
        hXR hcs hsK]
    ring
  · simp [hc]

/-- **High-prime band -> low-cofactor prime-window transform.**

The Mertens band from #570 is exactly the difference of two already-compiled
prime-dilate cofactor transforms.  Every cofactor above `sqrt R` vanishes
identically, so the signed sum may be restricted to the low cofactor carrier
before any norm is taken. -/
theorem highPrimeBand_windowTransform
    {p R K X : ℕ} (hp : p.Prime)
    (hXR : X ≤ R) (hsK : Nat.sqrt R ≤ K) :
    firstJumpPrimeSieveMertensBand (Nat.sqrt R) K X =
      ∑ c ∈ firstJumpHighPrimeCofactorSupport p R X,
        firstJumpHighPrimeCofactorResponse p R K X c *
          canonicalMoebiusWeight c := by
  have hfull :
      firstJumpPrimeSieveMertensBand (Nat.sqrt R) K X =
        ∑ c ∈ primeDilateCofactorSupport p X,
          firstJumpHighPrimeCofactorResponse p R K X c *
            canonicalMoebiusWeight c := by
    rw [firstJumpPrimeSieveMertensBand_eq_tail_sub_tail hsK,
      primeSieveMertensPrimeTail_eq_primeDilateCofactorPrimeCountTransform
        p (Nat.sqrt R) X hp,
      primeSieveMertensPrimeTail_eq_primeDilateCofactorPrimeCountTransform
        p K X hp]
    unfold primeDilateCofactorPrimeCountTransform
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    simp [firstJumpHighPrimeCofactorResponse, hc]
    ring
  rw [hfull]
  symm
  refine Finset.sum_subset Finset.inter_subset_left ?_
  intro c hcFull hcNotLow
  have hc1 : 1 ≤ c :=
    (mem_primeDilateCofactorSupport.mp hcFull).1
  have hcNotRoot : c ∉ Finset.Icc 1 (Nat.sqrt R) := by
    intro hcRoot
    exact hcNotLow (Finset.mem_inter.mpr ⟨hcFull, hcRoot⟩)
  have hcs : Nat.sqrt R < c := by
    by_contra hnot
    have hcle : c ≤ Nat.sqrt R := Nat.le_of_not_gt hnot
    exact hcNotRoot (Finset.mem_Icc.mpr ⟨hc1, hcle⟩)
  rw [firstJumpHighPrimeCofactorResponse_eq_zero_of_sqrt_lt_cofactor
    hXR hsK hcs]
  simp

/-- **Endpoint difference on one low-cofactor carrier.**  The first-jump
residual is now literally Möbius parity paired with the change in an explicit
prime-window response. -/
theorem sqrtFirstJumpResidual_cast_eq_cofactorWindowDifference
    {p R q A B : ℕ} (hp : p.Prime)
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      ∑ c ∈ firstJumpHighPrimeCofactorSupport p R B,
        canonicalMoebiusWeight c *
          (firstJumpHighPrimeCofactorResponse p R (q - 1) A c -
            firstJumpHighPrimeCofactorResponse p R (q - 1) B c) := by
  have hAR : A ≤ R := hAB.trans hBR
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  rw [sqrtFirstJumpResidual_cast_eq_band_sub_band hqroot hBR hAB,
    highPrimeBand_windowTransform hp hAR hsK,
    highPrimeBand_windowTransform hp hBR hsK]
  have hsub :
      firstJumpHighPrimeCofactorSupport p R A ⊆
        firstJumpHighPrimeCofactorSupport p R B :=
    firstJumpHighPrimeCofactorSupport_mono hAB
  have hAextend :
      (∑ c ∈ firstJumpHighPrimeCofactorSupport p R A,
          firstJumpHighPrimeCofactorResponse p R (q - 1) A c *
            canonicalMoebiusWeight c) =
        ∑ c ∈ firstJumpHighPrimeCofactorSupport p R B,
          firstJumpHighPrimeCofactorResponse p R (q - 1) A c *
            canonicalMoebiusWeight c := by
    refine Finset.sum_subset hsub ?_
    intro c hcB hcNotA
    have hcRoot := (Finset.mem_inter.mp hcB).2
    have hcNotSupportA : c ∉ primeDilateCofactorSupport p A := by
      intro hcA
      exact hcNotA (Finset.mem_inter.mpr ⟨hcA, hcRoot⟩)
    simp [firstJumpHighPrimeCofactorResponse, hcNotSupportA]
  rw [hAextend, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  ring

/-- Increasing the prime cutoff only removes points from a fixed prime-dilate
window. -/
theorem primeDilateCofactorWindow_mono_cutoff
    {p s K X c : ℕ} (hsK : s ≤ K) :
    primeDilateCofactorWindow p K X c ⊆
      primeDilateCofactorWindow p s X c := by
  intro q hq
  rcases mem_primeDilateCofactorWindow.mp hq with ⟨hlo, hup⟩
  apply mem_primeDilateCofactorWindow.mpr
  refine ⟨?_, hup⟩
  unfold primeDilateCofactorWindowLower at hlo ⊢
  have hmax :
      max s (X / (p * c)) ≤ max K (X / (p * c)) := by
    exact max_le
      (hsK.trans (le_max_left _ _))
      (le_max_right _ _)
  exact hmax.trans_lt hlo

/-- Literal prime support of one cofactor's high-prime band. -/
def firstJumpHighPrimeCofactorWindowSet
    (p R K X c : ℕ) : Finset ℕ :=
  (primeDilateCofactorWindow p (Nat.sqrt R) X c \
      primeDilateCofactorWindow p K X c).filter Nat.Prime

/-- Its exact prime-indicator mass. -/
def firstJumpHighPrimeCofactorWindowMass
    (p R K X c : ℕ) : ℂ :=
  ∑ q ∈ primeDilateCofactorWindow p (Nat.sqrt R) X c \
      primeDilateCofactorWindow p K X c,
    primeSievePrimeIndicator q

/-- On an active cofactor the response is exactly the mass of the set-difference
window. -/
theorem firstJumpHighPrimeCofactorResponse_eq_windowMass
    {p R K X c : ℕ}
    (hsK : Nat.sqrt R ≤ K)
    (hc : c ∈ primeDilateCofactorSupport p X) :
    firstJumpHighPrimeCofactorResponse p R K X c =
      firstJumpHighPrimeCofactorWindowMass p R K X c := by
  unfold firstJumpHighPrimeCofactorResponse
  simp only [hc, if_true]
  unfold firstJumpHighPrimeCofactorWindowMass
    primeDilateCofactorWindowPrimeCount
  have hsub :
      primeDilateCofactorWindow p K X c ⊆
        primeDilateCofactorWindow p (Nat.sqrt R) X c :=
    primeDilateCofactorWindow_mono_cutoff hsK
  have hs := Finset.sum_sdiff hsub (f := primeSievePrimeIndicator)
  linear_combination hs

/-- The window mass is literally the cardinality of its prime support. -/
theorem firstJumpHighPrimeCofactorWindowMass_eq_card
    (p R K X c : ℕ) :
    firstJumpHighPrimeCofactorWindowMass p R K X c =
      (((firstJumpHighPrimeCofactorWindowSet p R K X c).card : ℕ) : ℂ) := by
  unfold firstJumpHighPrimeCofactorWindowMass
    firstJumpHighPrimeCofactorWindowSet
  simp [primeSievePrimeIndicator, Finset.sum_boole]

/-- **Comparison with the existing canonical rough-prime carrier.**

At an endpoint `X <= R`, every prime in a retained first-jump cofactor window is
already a canonical rough-prime partner at the next complete-square root
`sqrt R + 1`.  Thus the new response is a windowed subcarrier of the existing
`SquareRootCanonicalRoughCovariance` response field; it is not promoted to a
new covariance object. -/
theorem firstJumpHighPrimeCofactorWindowSet_subset_canonicalRoughPrimePartnerSet
    {p R K X c : ℕ} (hR : 0 < R) (hXR : X ≤ R)
    (hc : c ∈ firstJumpHighPrimeCofactorSupport p R X) :
    firstJumpHighPrimeCofactorWindowSet p R K X c ⊆
      squareRootCanonicalRoughPrimePartnerSet (Nat.sqrt R + 1) c := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqDiff, hqPrime⟩
  have hqWindow := (Finset.mem_sdiff.mp hqDiff).1
  rcases mem_primeDilateCofactorWindow.mp hqWindow with ⟨hlo, hup⟩
  rcases Finset.mem_inter.mp hc with ⟨hcSupport, hcRoot⟩
  rcases mem_primeDilateCofactorSupport.mp hcSupport with
    ⟨hc1, _hcX, _hfree⟩
  have hcpos : 0 < c := by omega
  have hcle : c ≤ Nat.sqrt R :=
    (Finset.mem_Icc.mp hcRoot).2
  have hsltq : Nat.sqrt R < q := by
    have hsLower :
        Nat.sqrt R ≤
          primeDilateCofactorWindowLower p (Nat.sqrt R) X c := by
      unfold primeDilateCofactorWindowLower
      exact le_max_left _ _
    exact hsLower.trans_lt hlo
  have hrough : canonicalLargestPrimeFactor c < q := by
    by_cases hcEq : c = 1
    · subst c
      simpa [canonicalLargestPrimeFactor] using hqPrime.one_lt
    · have hcgt : 1 < c := by omega
      exact (canonicalLargestPrimeFactor_le_self hcgt).trans_lt
        (hcle.trans_lt hsltq)
  unfold primeDilateCofactorWindowUpper at hup
  have hqcX : q * c ≤ X :=
    (Nat.le_div_iff_mul_le hcpos).1 hup
  have hcqX : c * q ≤ X := by
    simpa [Nat.mul_comm] using hqcX
  have hqRoot : Nat.sqrt R + 1 ≤ q := by omega
  have hrootProduct : Nat.sqrt R + 1 ≤ c * q := by
    have hqle : q ≤ c * q := by
      simpa using Nat.mul_le_mul_right q hc1
    exact hqRoot.trans hqle
  have hclock : R < (Nat.sqrt R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hRupper : R ≤ squareRootEndpoint (Nat.sqrt R + 1) := by
    unfold squareRootEndpoint
    omega
  have hcqUpper : c * q ≤ squareRootEndpoint (Nat.sqrt R + 1) :=
    hcqX.trans (hXR.trans hRupper)
  have hspos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 hR
  have hrootTwo : 2 ≤ Nat.sqrt R + 1 := by omega
  exact
    (mem_squareRootCanonicalRoughPrimePartnerSet_iff hrootTwo hcpos).2
      ⟨hqPrime, hrough, hrootProduct, hcqUpper⟩

/-- Cardinality comparison with the already-existing canonical rough-prime
response carrier. -/
theorem firstJumpHighPrimeCofactorWindowSet_card_le_canonicalRoughPrimePartnerSet
    {p R K X c : ℕ} (hR : 0 < R) (hXR : X ≤ R)
    (hc : c ∈ firstJumpHighPrimeCofactorSupport p R X) :
    (firstJumpHighPrimeCofactorWindowSet p R K X c).card ≤
      (squareRootCanonicalRoughPrimePartnerSet (Nat.sqrt R + 1) c).card :=
  Finset.card_le_card
    (firstJumpHighPrimeCofactorWindowSet_subset_canonicalRoughPrimePartnerSet
      hR hXR hc)

end RHLean.Proof

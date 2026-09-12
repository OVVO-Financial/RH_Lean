import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Proof.TerminalMertensReduction
import RHLean.Proof.SignedTransportAmplificationAudit

/-!
# Discharge the terminal forward Mertens criterion

The analytic continuation, identity theorem, and completed-zeta reflection now
construct the one direction of the classical Mertens criterion that the terminal
proof actually uses.  This file plugs that theorem into
`TerminalMertensReduction` and records the resulting unconditional implication
from the projected-renewal estimate to Mathlib's Riemann Hypothesis.

The reverse implication `RH → MertensEnergyBoundedStatement` is not needed by
this forward route and is not asserted here.

The final section records the first global consequence of the fresh-prime
rough-partner boundary law.  Along a single ancestry chain, signed
`Loss - Birth` boundaries telescope to endpoint capacities.  After root
crossing, births vanish edgewise, so the positive loss mass itself telescopes.
This removes ancestry depth as a source of multiplicity, but deliberately makes
no claim about multiplicity across distinct branches.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

namespace TerminalMertensForward

open RHLean.Analysis
open CanonicalGapAncestryQuadraticClosure
open TerminalMertensReduction

/-- The previously external forward Mertens criterion is now constructed from
the repository's Mellin continuation and completed-zeta reflection. -/
theorem mertensForwardCriterion : MertensForwardCriterion := by
  intro hM
  change RiemannHypothesis
  exact riemannHypothesis_of_mertensEnergy hM

/-- **Square-prefix terminal theorem.**  Once the exact square-prefix Mertens
energy estimate is proved, the existing square-to-global bridge and the
unconditional forward Mertens theorem give Mathlib's Riemann Hypothesis.  No
`ClassicalMertensRHCriterion` argument is used. -/
theorem riemannHypothesis_of_squarePrefixEnergy
    (hS : SquarePrefixEnergyBoundedStatement) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_squarePrefixEnergyBounded hS)

/-- Consequently the terminal implication no longer needs a classical
Mertens/RH criterion supplied by the caller. Once the projected-renewal
quadratic estimate is proved, RH follows outright. -/
theorem projectedRenewalQuadraticBounded_imp_riemannHypothesis_unconditional
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ProjectedRenewalQuadraticBoundedStatement Λ →
      RiemannHypothesisStatement :=
  projectedRenewalQuadraticBounded_imp_riemannHypothesis
    hΛ mertensForwardCriterion

end TerminalMertensForward

namespace CanonicalRoughPartnerAncestryBoundary

open RHLean.Analysis

private theorem complex_sum_range_forwardDifference
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Along any multiplicative ancestry chain, the complete signed finite
boundary `Loss - Birth` telescopes to the difference of endpoint rough-partner
capacities.  No root-crossing or primality hypothesis is needed for this purely
set-theoretic aggregation of the exact one-edge law. -/
theorem squareRootCanonicalRoughFreshBoundary_chain_telescope
    {R n : ℕ} (c p : ℕ → ℕ)
    (hstep : ∀ i, i < n → c (i + 1) = p i * c i) :
    (∑ i ∈ Finset.range n,
        (((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ))) =
      squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
  calc
    (∑ i ∈ Finset.range n,
        (((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ))) =
      ∑ i ∈ Finset.range n,
        (squareRootCanonicalRoughPrimePartnerCount R (c i) -
          squareRootCanonicalRoughPrimePartnerCount R (c (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hedge :=
          squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_loss_sub_birth
            (R := R) (c := c i) (p := p i)
        rw [← hstep i hin] at hedge
        exact hedge.symm
    _ = squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
      simpa using complex_sum_range_forwardDifference
        (fun i => squareRootCanonicalRoughPrimePartnerCount R (c i)) n

/-- On a chain segment whose fresh-prime children have all reached the root,
every birth boundary is empty. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_chain_sum_eq_zero_of_root_reached
    {R n : ℕ} (c p : ℕ → ℕ)
    (hR : 2 ≤ R)
    (hc : ∀ i, i < n → 0 < c i)
    (hp : ∀ i, i < n → (p i).Prime)
    (hfresh : ∀ i, i < n → canonicalLargestPrimeFactor (c i) < p i)
    (hroot : ∀ i, i < n → R ≤ p i * c i) :
    (∑ i ∈ Finset.range n,
        ((squareRootCanonicalRoughFreshBirthBoundary R (c i) (p i)).card : ℂ)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  rw [squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
    (hR := hR) (hc := hc i hin) (hp := hp i hin)
    (hfresh := hfresh i hin) (hroot := hroot i hin)]
  simp

/-- **Post-root ancestry telescope.**  Along any fresh-prime chain segment for
which every child is at or beyond `R`, the positive sum of loss-boundary
cardinalities is exactly the difference of the endpoint rough-partner
capacities.  Hence ancestry depth contributes no extra post-root multiplicity
on a single branch. -/
theorem squareRootCanonicalRoughFreshLossBoundary_chain_telescope_of_root_reached
    {R n : ℕ} (c p : ℕ → ℕ)
    (hR : 2 ≤ R)
    (hc : ∀ i, i < n → 0 < c i)
    (hp : ∀ i, i < n → (p i).Prime)
    (hfresh : ∀ i, i < n → canonicalLargestPrimeFactor (c i) < p i)
    (hstep : ∀ i, i < n → c (i + 1) = p i * c i)
    (hroot : ∀ i, i < n → R ≤ p i * c i) :
    (∑ i ∈ Finset.range n,
        ((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ)) =
      squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
  calc
    (∑ i ∈ Finset.range n,
        ((squareRootCanonicalRoughFreshLossBoundary R (c i) (p i)).card : ℂ)) =
      ∑ i ∈ Finset.range n,
        (squareRootCanonicalRoughPrimePartnerCount R (c i) -
          squareRootCanonicalRoughPrimePartnerCount R (c (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hedge :=
          squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_lossBoundary
            (R := R) (c := c i) (p := p i)
            hR (hc i hin) (hp i hin) (hfresh i hin) (hroot i hin)
        rw [← hstep i hin] at hedge
        exact hedge.symm
    _ = squareRootCanonicalRoughPrimePartnerCount R (c 0) -
        squareRootCanonicalRoughPrimePartnerCount R (c n) := by
      simpa using complex_sum_range_forwardDifference
        (fun i => squareRootCanonicalRoughPrimePartnerCount R (c i)) n

end CanonicalRoughPartnerAncestryBoundary

/-! ## Literal q² endpoint recurrence closes outright -/

open RHLean.Analysis RHLean.Arithmetic

/-- Literal odd-owner q² recurrence before square-endpoint shell interpolation. -/
def SquareEndpointRawOddQ2EnergyStep (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    2 ≤ R →
    LowerMertensCriticalEnvelope R K →
    squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K +
        4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q

private theorem rawOddQ2Owner_card_le_root (R : ℕ) :
    ((primesUpTo (R - 1)).erase 2).card ≤ R := by
  let S : Finset ℕ := (primesUpTo (R - 1)).erase 2
  have hsub : S ⊆ Finset.range R := by
    intro q hq
    have hq' : q ∈ primesUpTo (R - 1) := (Finset.mem_erase.mp hq).2
    have hqle := (mem_primesUpTo.mp hq').2
    exact Finset.mem_range.mpr (by omega)
  simpa [S] using Finset.card_le_card hsub

/-- The total deterministic shell width has root-energy scale. -/
theorem sum_roundedQ2ChildRoot_succ_sq_le_two_root_sq
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ q ∈ (primesUpTo (R - 1)).erase 2,
      (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
        2 * (R : ℝ) ^ 2 := by
  let S : Finset ℕ := (primesUpTo (R - 1)).erase 2
  have hpoint : ∀ q ∈ S,
      (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 ≤
        2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2 := by
    intro q hq
    nlinarith [sq_nonneg (((roundedQ2ChildRoot R q : ℕ) : ℝ) - 1)]
  have hsum :
      (∑ q ∈ S, (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
        ∑ q ∈ S, (2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2) := by
    apply Finset.sum_le_sum
    intro q hq
    exact hpoint q hq
  have hsumId :
      (∑ q ∈ S, (2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2)) =
        2 * (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
          2 * (S.card : ℝ) := by
    rw [Finset.sum_add_distrib]
    simp [Finset.mul_sum]
    ring
  have hscale := sum_roundedQ2ChildRoot_sq_le_seventeen_over_seventy_two R
  change (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) ≤
    (17 : ℝ) / 72 * (R : ℝ) ^ 2 at hscale
  have hcardNat : S.card ≤ R := by
    simpa [S] using rawOddQ2Owner_card_le_root R
  have hcard : (S.card : ℝ) ≤ (R : ℝ) := by exact_mod_cast hcardNat
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  calc
    (∑ q ∈ S, (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
        ∑ q ∈ S, (2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2) := hsum
    _ = 2 * (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
          2 * (S.card : ℝ) := hsumId
    _ ≤ 2 * ((17 : ℝ) / 72 * (R : ℝ) ^ 2) + 2 * (R : ℝ) := by
      nlinarith
    _ ≤ 2 * (R : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((R : ℝ) - 2)]

private theorem rawRoundedQ2ChildRoot_lt_parent
    {R q : ℕ} (hR : 1 ≤ R) :
    roundedQ2ChildRoot R q < R := by
  unfold roundedQ2ChildRoot
  apply (Nat.sqrt_lt').2
  have hle : squareRootEndpoint R / (q * q) ≤ squareRootEndpoint R :=
    Nat.div_le_self _ _
  have hsqPos : 0 < R ^ 2 := by positivity
  have hend : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    exact Nat.sub_lt hsqPos (by norm_num)
  exact hle.trans_lt hend

private theorem rawLowerEnvelope_mono_root
    {R S : ℕ} {K : ℝ}
    (hSR : S < R)
    (hK : LowerMertensCriticalEnvelope R K) :
    LowerMertensCriticalEnvelope S K := by
  refine ⟨hK.1, ?_⟩
  intro y hy
  exact hK.2 y (hy.trans hSR)

private theorem rawSquareEndpointEnergy_eq_zero_of_lt_two
    {R : ℕ} (hR : R < 2) :
    squareEndpointMertensEnergyReal R = 0 := by
  interval_cases R <;>
    simp [squareEndpointMertensEnergyReal, squareRootEndpoint,
      mertensSummatoryInt]

/-- A literal factor-four q² recurrence already gives a fixed square-root
amplification.  The shell changes the recursive coefficient from `17/18` to
`629/648 < 1`; its entire unsigned remainder is absorbed into the additive
root-energy term. -/
theorem squareEndpointRawOddQ2EnergyStep_implies_unshifted_amplification
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRawOddQ2EnergyStep C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ R : ℕ, ∀ K : ℝ,
        2 ≤ R →
        LowerMertensCriticalEnvelope R K →
        squareEndpointMertensEnergyReal R ≤ A * (R : ℝ) ^ 2 * K := by
  let A : ℝ := (648 : ℝ) / 19 * (C + 1184)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro K hR hK
      let S : Finset ℕ := (primesUpTo (R - 1)).erase 2
      have hK0 : 0 ≤ K := hK.1
      have hK1 : 1 ≤ K := by
        have h0 := hK.2 0 (by omega)
        have hm0 : mertensSummatoryInt 0 = 0 := by
          simp [mertensSummatoryInt]
        rw [hm0] at h0
        norm_num at h0
        exact h0
      have hchild : ∀ q ∈ S,
          squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) ≤
            A * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 * K := by
        intro q hq
        have hsR : roundedQ2ChildRoot R q < R :=
          rawRoundedQ2ChildRoot_lt_parent (by omega)
        by_cases hs2 : 2 ≤ roundedQ2ChildRoot R q
        · exact ih (roundedQ2ChildRoot R q) hsR K hs2
            (rawLowerEnvelope_mono_root hsR hK)
        · have hslt : roundedQ2ChildRoot R q < 2 := by omega
          rw [rawSquareEndpointEnergy_eq_zero_of_lt_two hslt]
          positivity
      have hrawTerms : ∀ q ∈ S,
          rawQ2ChildEnergyReal R q ≤
            ((37 : ℝ) / 36 * A * K) *
                ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 +
              148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := by
        intro q hq
        have hshell :=
          rawQ2ChildEnergyReal_le_thirtySeven_thirtySix_rounded_add_shell R q
        have hc := hchild q hq
        calc
          rawQ2ChildEnergyReal R q ≤
              (37 : ℝ) / 36 *
                  squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) +
                148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := hshell
          _ ≤ (37 : ℝ) / 36 *
                  (A * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 * K) +
                148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := by
              gcongr
          _ = ((37 : ℝ) / 36 * A * K) *
                  ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 +
                148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := by ring
      have hrawSum :
          (∑ q ∈ S, rawQ2ChildEnergyReal R q) ≤
            ((37 : ℝ) / 36 * A * K) *
                (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
              148 * (∑ q ∈ S,
                (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) := by
        calc
          (∑ q ∈ S, rawQ2ChildEnergyReal R q) ≤
              ∑ q ∈ S,
                (((37 : ℝ) / 36 * A * K) *
                    ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 +
                  148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) := by
                    apply Finset.sum_le_sum
                    intro q hq
                    exact hrawTerms q hq
          _ = ((37 : ℝ) / 36 * A * K) *
                (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
              148 * (∑ q ∈ S,
                (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) := by
                  rw [Finset.sum_add_distrib]
                  rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hscale := sum_roundedQ2ChildRoot_sq_le_seventeen_over_seventy_two R
      change (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) ≤
        (17 : ℝ) / 72 * (R : ℝ) ^ 2 at hscale
      have hshellSum := sum_roundedQ2ChildRoot_succ_sq_le_two_root_sq R hR
      change (∑ q ∈ S,
        (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
          2 * (R : ℝ) ^ 2 at hshellSum
      have hcoef : 0 ≤ (37 : ℝ) / 36 * A * K := by
        exact mul_nonneg (mul_nonneg (by norm_num) hA) hK0
      have hrawSum' :
          (∑ q ∈ S, rawQ2ChildEnergyReal R q) ≤
            ((37 : ℝ) / 36 * A * K) *
                ((17 : ℝ) / 72 * (R : ℝ) ^ 2) +
              148 * (2 * (R : ℝ) ^ 2) := by
        exact hrawSum.trans (add_le_add
          (mul_le_mul_of_nonneg_left hscale hcoef)
          (mul_le_mul_of_nonneg_left hshellSum (by norm_num)))
      have hs := hstep R K hR hK
      change squareEndpointMertensEnergyReal R ≤
        C * (R : ℝ) ^ 2 * K +
          4 * ∑ q ∈ S, rawQ2ChildEnergyReal R q at hs
      have hweighted := mul_le_mul_of_nonneg_left hrawSum'
        (by norm_num : (0 : ℝ) ≤ 4)
      have hadd :
          1184 * (R : ℝ) ^ 2 ≤ 1184 * (R : ℝ) ^ 2 * K := by
        have hnonneg : 0 ≤ 1184 * (R : ℝ) ^ 2 := by positivity
        nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hK1)]
      have hfixed : C + 1184 + (629 : ℝ) / 648 * A = A := by
        dsimp [A]
        ring
      calc
        squareEndpointMertensEnergyReal R ≤
            C * (R : ℝ) ^ 2 * K +
              4 * ∑ q ∈ S, rawQ2ChildEnergyReal R q := hs
        _ ≤ C * (R : ℝ) ^ 2 * K +
              4 * (((37 : ℝ) / 36 * A * K) *
                  ((17 : ℝ) / 72 * (R : ℝ) ^ 2) +
                148 * (2 * (R : ℝ) ^ 2)) := add_le_add_left hweighted _
        _ = (C + (629 : ℝ) / 648 * A) * ((R : ℝ) ^ 2 * K) +
              1184 * (R : ℝ) ^ 2 := by ring
        _ ≤ (C + 1184 + (629 : ℝ) / 648 * A) *
              ((R : ℝ) ^ 2 * K) := by
                nlinarith
        _ = A * (R : ℝ) ^ 2 * K := by rw [hfixed]; ring

/-- The literal q² recurrence therefore supplies exactly the endpoint
amplification interface consumed by the unconditional Mertens closure. -/
theorem squareEndpointRawOddQ2EnergyStep_implies_endpointAmplification
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRawOddQ2EnergyStep C) :
    SquareRootMertensEndpointAmplificationStatement := by
  rcases squareEndpointRawOddQ2EnergyStep_implies_unshifted_amplification
      hC hstep with ⟨A, hA, hbound⟩
  refine ⟨2 * A + 1, by positivity, ?_⟩
  intro R K hR hK
  have hM := hbound R K hR hK
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  let m : ℝ := ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)
  have hM' : m ^ 2 ≤ A * (R : ℝ) ^ 2 * K := by
    simpa [m, squareEndpointMertensEnergyReal] using hM
  have hshift : (m - 1) ^ 2 ≤ 2 * m ^ 2 + 2 := by
    nlinarith [sq_nonneg (m + 1)]
  have hscale : 2 ≤ (R : ℝ) ^ 2 * K := by
    have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    nlinarith [mul_le_mul_of_nonneg_left hK1 (sq_nonneg (R : ℝ))]
  have hmshift :
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) = m - 1 := by
    dsimp [m]
    push_cast
    ring
  rw [hmshift]
  calc
    (m - 1) ^ 2 ≤ 2 * m ^ 2 + 2 := hshift
    _ ≤ 2 * (A * (R : ℝ) ^ 2 * K) + 2 := by nlinarith [hM']
    _ ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K := by nlinarith

/-- Fixed endpoint amplification already implies the existence of a raw q²
recurrence constant.  This converse is deliberately elementary: the lower
envelope forces `K >= 1`, the unshifted endpoint costs only a factor two plus a
constant, and the q² child energy is nonnegative.  Thus the raw recurrence is
not a weaker local bookkeeping target; up to absolute constants it is the
endpoint amplification theorem itself. -/
theorem squareRootEndpointAmplification_implies_exists_rawOddQ2EnergyStep
    (hamp : SquareRootMertensEndpointAmplificationStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ SquareEndpointRawOddQ2EnergyStep C := by
  rcases hamp with ⟨A, hA, hbound⟩
  refine ⟨2 * A + 1, by positivity, ?_⟩
  intro R K hR hK
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  let m : ℝ := ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)
  have hmshift :
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) = m - 1 := by
    dsimp [m]
    push_cast
    ring
  have hshifted := hbound R K hR hK
  rw [hmshift] at hshifted
  have hm : m ^ 2 ≤ 2 * (m - 1) ^ 2 + 2 := by
    nlinarith [sq_nonneg (m - 2)]
  have hscale : 2 ≤ (R : ℝ) ^ 2 * K := by
    have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    nlinarith [mul_le_mul_of_nonneg_left hK1 (sq_nonneg (R : ℝ))]
  have hmBound : m ^ 2 ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K := by
    calc
      m ^ 2 ≤ 2 * (m - 1) ^ 2 + 2 := hm
      _ ≤ 2 * (A * (R : ℝ) ^ 2 * K) + 2 := by nlinarith [hshifted]
      _ ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K := by nlinarith
  have hparent :
      squareEndpointMertensEnergyReal R ≤
        (2 * A + 1) * (R : ℝ) ^ 2 * K := by
    simpa [m, squareEndpointMertensEnergyReal] using hmBound
  have hchildren0 :
      0 ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        rawQ2ChildEnergyReal R q := by
    apply Finset.sum_nonneg
    intro q hq
    unfold rawQ2ChildEnergyReal
    positivity
  exact hparent.trans (by nlinarith)

/-- Existence of a nonnegative literal factor-four q² recurrence constant is
**equivalent** to fixed square-root endpoint amplification.  The forward
implication is the genuine shell/induction theorem; the reverse implication is
the elementary padding theorem above.  This prevents the raw recurrence from
being mistaken for an independent weaker seam. -/
theorem exists_nonneg_squareEndpointRawOddQ2EnergyStep_iff_endpointAmplification :
    (∃ C : ℝ, 0 ≤ C ∧ SquareEndpointRawOddQ2EnergyStep C) ↔
      SquareRootMertensEndpointAmplificationStatement := by
  constructor
  · rintro ⟨C, hC, hstep⟩
    exact squareEndpointRawOddQ2EnergyStep_implies_endpointAmplification hC hstep
  · intro hamp
    exact squareRootEndpointAmplification_implies_exists_rawOddQ2EnergyStep hamp

/-- Consequently the literal signed factor-four recurrence is already an RH
criterion; no further square-shell or endpoint theorem remains after it. -/
theorem riemannHypothesis_of_squareEndpointRawOddQ2EnergyStep
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRawOddQ2EnergyStep C) :
    RiemannHypothesis := by
  apply RHLean.Analysis.riemannHypothesis_of_mertensEnergy
  exact mertensEnergyBounded_of_squareRootEndpointAmplification
    (squareEndpointRawOddQ2EnergyStep_implies_endpointAmplification hC hstep)

end RHLean.Proof

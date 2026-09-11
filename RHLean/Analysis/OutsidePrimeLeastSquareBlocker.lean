import Mathlib
import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo
import RHLean.Analysis.OutsidePrimeLeastSquareEndpoint

/-!
# Local least-square ownership and complete-super-orbit blocker

This module isolates two facts needed by the compensated q-square daughter
intertwining.

First, least-square ownership is genuinely local: `q` owns a physical edge
exactly when `q^2` hits one of the six active affine forms and no smaller prime
square does.  No ambient prefix occurs in the statement.

Second, if a q-owned deletion cell belongs to the complete least-owner interior
of one square block, then the exact least-owner super-orbit period is at most the
square-block length bound `2*R+2`.  Consequently any owner whose super-orbit
period is larger is forced into the aggregate incomplete endpoint.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- **Local ownership characterization.**  A prime `q` is the least square
owner of edge `k` iff it actually hits one active form and every smaller prime
fails to hit every active form.  The criterion contains no prefix parameter. -/
theorem physicalLeastOddSquarePrime_eq_some_iff_local
    {k q : ℕ} (hq : q.Prime) :
    physicalLeastOddSquarePrime k = some q ↔
      physicalSquarePrimeAtEdge k q ∧
        ∀ p : ℕ, p.Prime → p < q → ¬ physicalSquarePrimeAtEdge k p := by
  constructor
  · intro hleast
    refine ⟨physicalLeastOddSquarePrime_some_spec hleast, ?_⟩
    intro p hp hlt hpHit
    have hle := physicalLeastOddSquarePrime_le hleast hpHit
    omega
  · rintro ⟨hqHit, hsmall⟩
    classical
    have hex : ∃ p, physicalSquarePrimeAtEdge k p := ⟨q, hqHit⟩
    have hspec : physicalSquarePrimeAtEdge k (Nat.find hex) := Nat.find_spec hex
    have hle : Nat.find hex ≤ q := Nat.find_min' hex hqHit
    have hnotlt : ¬ Nat.find hex < q := by
      intro hlt
      exact hsmall (Nat.find hex) hspec.1 hlt hspec
    have heq : Nat.find hex = q := by omega
    simp [physicalLeastOddSquarePrime, hex, heq]

/-- **Complete-owner period bound.**  Any cell retained in the complete
least-owner interior with owner `q` carries its entire exact super-orbit inside
the physical square block.  Hence that super-orbit period is at most `2*R+2`. -/
theorem outsidePrimeLeastComplete_owner_period_le
    {P : Finset ℕ} {R q k : ℕ}
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R)
    (howner : physicalLeastOddSquarePrime k = some q) :
    finitePrimeCRTPeriod (outsidePrimeLeastSuperPrimeSet P q) ≤ 2 * R + 2 := by
  have hsub := (Finset.mem_filter.mp hk).2
  have hget : (physicalLeastOddSquarePrime k).getD 0 = q := by
    simp [howner]
  rw [hget] at hsub
  have hcard := Finset.card_le_card hsub
  unfold outsidePrimeLeastSuperOrbit at hcard
  rw [card_finitePrimeCRTOrbit] at hcard
  exact hcard.trans (card_threeSlotSquareBlockTransitionCells_le R)

/-- **Blocker interface.**  If the exact least-owner super-orbit period exceeds
one square block, owner `q` cannot occur in the complete interior. -/
theorem outsidePrimeLeastComplete_no_owner_of_period_gt
    {P : Finset ℕ} {R q k : ℕ}
    (hperiod : 2 * R + 2 <
      finitePrimeCRTPeriod (outsidePrimeLeastSuperPrimeSet P q))
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R) :
    physicalLeastOddSquarePrime k ≠ some q := by
  intro howner
  have hle := outsidePrimeLeastComplete_owner_period_le hk howner
  omega

/-! ## Physical prime-13 and prime-17 weight-one layers

The abstract Walsh factors for every prime `p >= 11` are already proved in
`FinitePrimeTMixing`.  The missing physical bridge for `13` and `17` is finite:
certify the zero-free and signed coordinate masses on `ZMod p^2`, then tensor
with an arbitrary complementary field exactly as for prime `11`.
-/

/-- Prime-13 zero-free indicator on the complete `13^2` residue coordinate. -/
def thirteenZeroFreeIndicatorZMod (z : ZMod 169) : ℚ :=
  if tSquareZeroFreeAt 13 z.val then 1 else 0

/-- Prime-13 signed coordinate multiplier with square-zero residues removed. -/
def thirteenZeroFreeCoordinateMultiplierZMod
    (i : Fin 6) (z : ZMod 169) : ℚ :=
  if tSquareZeroFreeAt 13 z.val then
    if 13 ∣ tTransitionForm i z.val then -1 else 1
  else 0

/-- There are exactly `169-6=163` zero-free prime-13 residues. -/
theorem sum_thirteenZeroFreeIndicatorZMod :
    (∑ z : ZMod 169, thirteenZeroFreeIndicatorZMod z) = 163 := by
  native_decide

/-- Every weight-one prime-13 coordinate has signed mass `163-2*12=139`. -/
theorem sum_thirteenZeroFreeCoordinateMultiplierZMod (i : Fin 6) :
    (∑ z : ZMod 169, thirteenZeroFreeCoordinateMultiplierZMod i z) = 139 := by
  fin_cases i <;> native_decide

@[simp] theorem onePrimeWalshFactor_thirteen_one :
    onePrimeWalshFactor 13 1 = (139 : ℚ) / 163 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

/-- **Deterministic complete-fibre prime-13 intertwining.**  The complementary
field is completely arbitrary; CRT alone separates the `13^2` coordinate. -/
theorem thirteen_coprimeTensor_firstMoment
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 169 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod (169 * M),
      thirteenZeroFreeCoordinateMultiplierZMod i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      onePrimeWalshFactor 13 1 *
        (∑ z : ZMod (169 * M),
          thirteenZeroFreeIndicatorZMod
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) := by
  have hsigned := coprimeZMod_sum_tensor 169 M hcop
    (thirteenZeroFreeCoordinateMultiplierZMod i) g
  have hzero := coprimeZMod_sum_tensor 169 M hcop
    thirteenZeroFreeIndicatorZMod g
  rw [sum_thirteenZeroFreeCoordinateMultiplierZMod] at hsigned
  rw [sum_thirteenZeroFreeIndicatorZMod] at hzero
  rw [hsigned, hzero, onePrimeWalshFactor_thirteen_one]
  ring

/-- Prime-13 rank-one energy multiplier. -/
theorem thirteen_coprimeTensor_firstMoment_sq
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 169 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod (169 * M),
      thirteenZeroFreeCoordinateMultiplierZMod i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) ^ 2 =
      (onePrimeWalshFactor 13 1) ^ 2 *
        (∑ z : ZMod (169 * M),
          thirteenZeroFreeIndicatorZMod
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) ^ 2 := by
  rw [thirteen_coprimeTensor_firstMoment M hcop i g]
  ring

/-- Prime-17 zero-free indicator on the complete `17^2` residue coordinate. -/
def seventeenZeroFreeIndicatorZMod (z : ZMod 289) : ℚ :=
  if tSquareZeroFreeAt 17 z.val then 1 else 0

/-- Prime-17 signed coordinate multiplier with square-zero residues removed. -/
def seventeenZeroFreeCoordinateMultiplierZMod
    (i : Fin 6) (z : ZMod 289) : ℚ :=
  if tSquareZeroFreeAt 17 z.val then
    if 17 ∣ tTransitionForm i z.val then -1 else 1
  else 0

/-- There are exactly `289-6=283` zero-free prime-17 residues. -/
theorem sum_seventeenZeroFreeIndicatorZMod :
    (∑ z : ZMod 289, seventeenZeroFreeIndicatorZMod z) = 283 := by
  native_decide

/-- Every weight-one prime-17 coordinate has signed mass `283-2*16=251`. -/
theorem sum_seventeenZeroFreeCoordinateMultiplierZMod (i : Fin 6) :
    (∑ z : ZMod 289, seventeenZeroFreeCoordinateMultiplierZMod i z) = 251 := by
  fin_cases i <;> native_decide

@[simp] theorem onePrimeWalshFactor_seventeen_one :
    onePrimeWalshFactor 17 1 = (251 : ℚ) / 283 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

/-- **Deterministic complete-fibre prime-17 intertwining.** -/
theorem seventeen_coprimeTensor_firstMoment
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 289 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod (289 * M),
      seventeenZeroFreeCoordinateMultiplierZMod i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      onePrimeWalshFactor 17 1 *
        (∑ z : ZMod (289 * M),
          seventeenZeroFreeIndicatorZMod
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) := by
  have hsigned := coprimeZMod_sum_tensor 289 M hcop
    (seventeenZeroFreeCoordinateMultiplierZMod i) g
  have hzero := coprimeZMod_sum_tensor 289 M hcop
    seventeenZeroFreeIndicatorZMod g
  rw [sum_seventeenZeroFreeCoordinateMultiplierZMod] at hsigned
  rw [sum_seventeenZeroFreeIndicatorZMod] at hzero
  rw [hsigned, hzero, onePrimeWalshFactor_seventeen_one]
  ring

/-- Prime-17 rank-one energy multiplier. -/
theorem seventeen_coprimeTensor_firstMoment_sq
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime 289 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod (289 * M),
      seventeenZeroFreeCoordinateMultiplierZMod i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) ^ 2 =
      (onePrimeWalshFactor 17 1) ^ 2 *
        (∑ z : ZMod (289 * M),
          seventeenZeroFreeIndicatorZMod
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) ^ 2 := by
  rw [seventeen_coprimeTensor_firstMoment M hcop i g]
  ring

/-- The three certified selected layers already give the advertised comfortable
weight-one amplitude contraction. -/
theorem eleven_thirteen_seventeen_weightOne_product_sq_lt_three_quarters :
    ((onePrimeWalshFactor 11 1) *
      (onePrimeWalshFactor 13 1) *
      (onePrimeWalshFactor 17 1)) ^ 2 < (3 : ℚ) / 4 := by
  rw [onePrimeWalshFactor_eleven_one,
    onePrimeWalshFactor_thirteen_one,
    onePrimeWalshFactor_seventeen_one]
  norm_num

end RHLean.Analysis

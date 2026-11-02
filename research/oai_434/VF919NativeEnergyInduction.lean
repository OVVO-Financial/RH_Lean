import OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor
import OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport
import «research.VF_919_OAI_ACTUAL_MARKED_FOURTH_REAL_NNS_20261021»

/-!
# Source-faithful replay of every certified energy stage in real NNS coordinates

This file replays the actual width induction from its proved floor and
analytic successor in RHLean partial-moment coordinates. It does not call the upstream
`terminal_certificate` or any terminal zero-free theorem.

The radial factor is retained with its sign. The coordinate equality is valid
for arbitrary radial profiles. Interpretation as an integral against a
positive measure additionally requires nonnegative real radial weights.
The analytic floor and successor are reused from the original proof; this
coordinate replay is not an independent proof of those analytic estimates.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.RHLeanNativeSevenEighthsReplay

open HeckeFamily
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCappedAnalyticSuccessor
open CenteredMomentEnergyCappedRadialTransport
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthInduction (lowerAt lengthAt)
open CenteredMomentInductionEnergy CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentPrimeSlot
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open ConcreteTraceCRT RHLean.Analysis

local notation "O" => HeckeFamily.O

/-- The degree-two UPM/LPM of both exact Phi channels, with the original
factor one half. The signed source is assembled before these moments. -/
def nativePartialSecond (z : ℂ) : ℝ :=
  let v := RHLean.Proof.stableFarComplexToRealPair z
  ((partialUpper v.1 0) ^ 2 + (partialLower v.1 0) ^ 2 +
    ((partialUpper v.2 0) ^ 2 + (partialLower v.2 0) ^ 2)) / 2

theorem nativePartialSecond_eq_realEnergy (z : ℂ) :
    nativePartialSecond z = vf919MarkedRealEnergy z := by
  have h₁ := vf919RowPartialSquare_reassembly
    (RHLean.Proof.stableFarComplexToRealPair z).1 0
  have h₂ := vf919RowPartialSquare_reassembly
    (RHLean.Proof.stableFarComplexToRealPair z).2 0
  simp only [sub_zero] at h₁ h₂
  unfold nativePartialSecond vf919MarkedRealEnergy
  dsimp only
  rw [h₁, h₂]

theorem nativePartialSecond_eq_normSq (z : ℂ) :
    nativePartialSecond z = ‖z‖ ^ 2 :=
  (nativePartialSecond_eq_realEnergy z).trans (vf919MarkedRealEnergy_eq_normSq z)

/-- Every original row, normalization, mask, selected ideal and radial weight
is unchanged; only its complete squared norm is written in real coordinates. -/
def nnsEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then
    nativePartialSecond
      (positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂) *
        (Φ (‖eisEmbedding z‖ ^ 2 / K)).re
    else 0

theorem nnsEnergy_eq_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K : ℝ) :
    nnsEnergy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K =
      energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  simp only [nnsEnergy, energy, nativePartialSecond_eq_normSq]

def nnsPlainEnergy {Z Bmask bΦ a b : ℝ}
    (s : NaturalState Z Bmask bΦ) (p : Profiles a b)
    (t X₁ X₂ : ℝ) : ℝ :=
  nnsEnergy s.character s.mask 1 t (p.profile 0) (p.profile 1)
    (fun _ : Fin 0 => ∅) (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 1)
    X₁ X₂ s.radial.keep s.radial.profile s.radial.scale

theorem nnsPlainEnergy_eq_plainEnergy {Z Bmask bΦ a b : ℝ}
    (s : NaturalState Z Bmask bΦ) (p : Profiles a b)
    (t X₁ X₂ : ℝ) :
    nnsPlainEnergy s p t X₁ X₂ = s.plainEnergy p t X₁ X₂ := by
  simp only [nnsPlainEnergy, NaturalState.plainEnergy, nnsEnergy_eq_energy]

def NNSZeroAt (Q : Ideal O) (a b bΦ Bmask L Mcap ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = Q → s.width ≤ Mcap →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    nnsPlainEnergy s p t X₁ X₂ ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 *
        (1 + ‖t‖) ^ degree * Z ^ (s.width + ε)

theorem nnsZeroAt_iff (Q : Ideal O) (a b bΦ Bmask L Mcap ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) :
    NNSZeroAt Q a b bΦ Bmask L Mcap ε Z degree S C ↔
      ZeroAt Q a b bΦ Bmask L Mcap ε Z degree S C := by
  simp only [NNSZeroAt, ZeroAt, nnsPlainEnergy_eq_plainEnergy]

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

def NNSPositiveAt (W : ℝ → ℂ)
    (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ)
    (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α,
  ∀ (θ : T → RayQuotient.Characters M H) (w σ v : T → ℝ)
    (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
    0 ≤ height → (∀ i, |v i| ≤ height) →
  ∀ s : NaturalState Z Bmask bΦ,
    s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    length Z X₁ + length Z X₂ + 6 * κ * (∑ i, w i) ≤ s.width →
    nnsEnergy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool M H bslot (Z ^ (w i)))
      (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
      (fun i => Z ^ (w i)) X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 *
        (1 + |t| + height) ^ degree * Z ^ (s.width + ε)

omit [Fintype α] in
theorem nnsPositiveAt_iff (W : ℝ → ℂ)
    (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ)
    (S : Finset (ℕ × ℕ)) (C : ℝ) :
    NNSPositiveAt (α := α) M H hH W
        bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C ↔
      PositiveAt (α := α) M H hH W
        bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C := by
  simp only [NNSPositiveAt, PositiveAt, nnsEnergy_eq_energy]

def NNSCertifiedBand (W : ℝ → ℂ)
    (bslot a b radial Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ) : Prop :=
  ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ),
  ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
    internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
    internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
  ∃ Czero Cpositive : ℝ, 0 < Czero ∧ 0 < Cpositive ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      NNSZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        Z degree S Czero ∧
      NNSPositiveAt (α := α) M H hH W
        bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        κ Z η₀ Q degree S Cpositive

theorem nnsCertifiedBand_iff (W : ℝ → ℂ)
    (bslot a b radial Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ) :
    NNSCertifiedBand (α := α) M H hH W
        bslot a b radial Bmask L lo hi Mcap κ ε k ↔
      CertifiedBand (α := α) M H hH W
        bslot a b radial Bmask L lo hi Mcap κ ε k := by
  simp only [NNSCertifiedBand, CertifiedBand, nnsZeroAt_iff, nnsPositiveAt_iff]

/-- Every induction level is a native real-energy statement, not only the
terminal conclusion. The two input theorems are the original proved analytic
floor and actual low/high/zero successor. -/
theorem nns_certified_bands
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0 < aslot)
    (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W)
    (hbslot : 0 ≤ bslot) (ha : 0 < a) (haUpper : a ≤ 1 / 4)
    (hb : 1 ≤ b) (hrad : 2 ≤ radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap)
    (hκ0 : (3 / 4 : ℝ) ≤ κ) (hε : 0 < ε)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2 * HeckeZeroSupremum.beta - 1 ≤ κ) :
    ∀ k : ℕ, k ≤ count Mcap ε →
      NNSCertifiedBand (α := α) M H hH W
        bslot a b radial Bmask L lo hi Mcap κ ε k := by
  intro k
  induction k with
  | zero =>
    intro _
    apply (nnsCertifiedBand_iff (α := α) M H hH W
      bslot a b radial Bmask L lo hi Mcap κ ε 0).mpr
    exact certified_floor (α := α) M H hH W
      aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith)
      hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious :=
      (nnsCertifiedBand_iff (α := α) M H hH W
        bslot a b radial Bmask L lo hi Mcap κ ε k).mp
        (ih (Nat.le_of_succ_le hk))
    apply (nnsCertifiedBand_iff (α := α) M H hH W
      bslot a b radial Bmask L lo hi Mcap κ ε (k + 1)).mpr
    exact actual_successor (α := α) M H hH W
      aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad
      hmask hMcap hκ0 hε hbeta hκ k (by omega) hprevious

theorem nns_certified_radial_mono (W : ℝ → ℂ)
    (bslot a b radialOld radialNew Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (hrad : radialNew ≤ radialOld)
    (h : NNSCertifiedBand (α := α) M H hH W
      bslot a b radialOld Bmask L lo hi Mcap κ ε k) :
    NNSCertifiedBand (α := α) M H hH W
      bslot a b radialNew Bmask L lo hi Mcap κ ε k := by
  apply (nnsCertifiedBand_iff (α := α) M H hH W
    bslot a b radialNew Bmask L lo hi Mcap κ ε k).mpr
  exact certified_radial_mono (α := α) M H hH W
    bslot a b radialOld radialNew Bmask L lo hi Mcap κ ε k hrad
    ((nnsCertifiedBand_iff (α := α) M H hH W
      bslot a b radialOld Bmask L lo hi Mcap κ ε k).mp h)

/-- Construct the terminal native state from the native induction above.
No upstream terminal certificate is invoked. -/
theorem nns_terminal_certificate
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0 < aslot)
    (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W)
    (hbslot : 0 ≤ bslot) (ha : 0 < a) (haUpper : a ≤ 1 / 4)
    (hb : 1 ≤ b) (_hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap)
    (hκ0 : (3 / 4 : ℝ) ≤ κ) (hε : 0 < ε)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2 * HeckeZeroSupremum.beta - 1 ≤ κ) :
    NNSCertifiedBand (α := α) M H hH W
      bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε) := by
  apply nns_certified_radial_mono (α := α) M H hH W
    bslot a b (max 2 radial) radial Bmask L lo hi Mcap κ ε
    (count Mcap ε) (le_max_right _ _)
  exact nns_certified_bands (α := α) M H hH W
    aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _)
    hmask hMcap hκ0 hε hbeta hκ _ le_rfl

#print axioms nativePartialSecond_eq_normSq
#print axioms nnsEnergy_eq_energy
#print axioms nns_certified_bands
#print axioms nns_terminal_certificate

end SevenEighths.RHLeanNativeSevenEighthsReplay
end
end OAI


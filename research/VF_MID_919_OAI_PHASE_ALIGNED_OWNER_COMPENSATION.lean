import Mathlib
import «research.GLOBAL_RETURNED_CORE_COMPENSATED_FOUR_CORNER»
import «research.STABLE_FAR_PERRON_REALIFICATION»
import «research.VF_MID_919_OAI_FERMAT_TWIST_PROJECTION»

/-!
# Phase-aligned compensation on the actual first-owner carrier

Twisting physical sites before fresh-prime compensation is not the same as
twisting the compensated parent afterwards. The former has an exact extra
term proportional to `1 - chi p`. On a nonzero multiplicative row the inverse
prime phase removes that term. The actual p-child bijection then reassembles
the entire cell into the phase-twisted native compensated interior PLUS the
literal clipped exit, before any energy is taken.

The interior Hermitian Gram is the original physical four-corner population
with kernel `Re(chi a * conj(chi b))`. The full cell square retains its clipped
square and interior/clipped mixed term. This is an exact finite native-carrier
interface, not an identification with OAI's Eisenstein-ideal probe or the full
historical Sector Six, and not a character-moment power saving.

The site weight here is precisely `lowOwnerZeroFrequencyMobiusWeight`, the
native returned-core AMP common-clock coefficient. It is NOT silently
identified with the original VF square-band weight.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- Character attached to the actual signed weighted physical site. -/
def vf919CharacterMobiusSite (R : ℕ) (chi : ℕ → ℂ) (n : ℕ) : ℂ :=
  (lowOwnerZeroFrequencyMobiusSite R n : ℂ) * chi n

/-- Phase-aligned sum of a physical parent and its admitted p-child. -/
def vf919CharacterAlignedSite (R p : ℕ) (chi : ℕ → ℂ) (a : ℕ) : ℂ :=
  vf919CharacterMobiusSite R chi a +
    (chi p)⁻¹ * vf919CharacterMobiusSite R chi (p * a)

/-- Parent phase retained on the literal native daughter/root difference. -/
def vf919ParentTwistedCompensatedSite
    (R p : ℕ) (chi : ℕ → ℂ) (a : ℕ) : ℂ :=
  (lowOwnerFirstOwnerCompensatedSite R p a : ℂ) * chi a

/-- Unaligned twisting creates a genuine extra term, even when the native
weight is constant. No nonzero-phase hypothesis is needed for this identity. -/
theorem vf919CharacterUnalignedSite_eq_compensated_add_phaseDefect
    {R p a : ℕ} (chi : ℕ → ℂ) (hp : p.Prime) (ha : ¬ p ∣ a)
    (hmul : chi (p * a) = chi p * chi a) :
    vf919CharacterMobiusSite R chi a +
        vf919CharacterMobiusSite R chi (p * a) =
      vf919ParentTwistedCompensatedSite R p chi a +
        (1 - chi p) *
          ((lowOwnerZeroFrequencyMobiusWeight R (p * a) *
            realMoebiusStep a : ℝ) : ℂ) * chi a := by
  unfold vf919CharacterMobiusSite vf919ParentTwistedCompensatedSite
    lowOwnerZeroFrequencyMobiusSite lowOwnerFirstOwnerCompensatedSite
  rw [realMoebiusStep_mul_prime_eq_neg hp ha, hmul,
    ← lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le]
  push_cast
  ring

/-- Exact local operator intertwining on an unramified multiplicative row.
The native moving weight remains on both physical sites throughout. -/
theorem vf919CharacterAlignedSite_eq_parentTwisted
    {R p a : ℕ} (chi : ℕ → ℂ) (hp : p.Prime) (ha : ¬ p ∣ a)
    (hphase : chi p ≠ 0) (hmul : chi (p * a) = chi p * chi a) :
    vf919CharacterAlignedSite R p chi a =
      vf919ParentTwistedCompensatedSite R p chi a := by
  unfold vf919CharacterAlignedSite vf919CharacterMobiusSite
    vf919ParentTwistedCompensatedSite lowOwnerZeroFrequencyMobiusSite
    lowOwnerFirstOwnerCompensatedSite
  rw [realMoebiusStep_mul_prime_eq_neg hp ha, hmul,
    ← lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le]
  push_cast
  field_simp [hphase] <;> ring

/-- A zero prime phase has no inverse cancellation: its child site vanishes
and the surviving source is the parent. This is separate from the good-row
identity and does not claim to represent OAI's ramified analytic remainder. -/
theorem vf919CharacterAlignedSite_of_zero_prime_phase
    (R p a : ℕ) (chi : ℕ → ℂ) (hphase : chi p = 0)
    (hmul : chi (p * a) = chi p * chi a) :
    vf919CharacterAlignedSite R p chi a =
      vf919CharacterMobiusSite R chi a := by
  simp [vf919CharacterAlignedSite, vf919CharacterMobiusSite, hphase, hmul]

/-- The actual child carrier is returned to admitted parents without changing
any occurrence or coefficient. The statement works for ANY complex site field. -/
theorem vf919FirstOwnerChild_sum_eq_returnedParents
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) (f : ℕ → ℂ) :
    (∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig, f n) =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig, f (p * a) := by
  refine Finset.sum_bij (fun n _hn => n / p)
    (fun n hn => lowOwnerFirstOwner_div_mem_admitted_of_child hp hn) ?_ ?_ ?_
  · intro n hn m hm heq
    have hnDvd := (Finset.mem_filter.mp hn).2.2
    have hmDvd := (Finset.mem_filter.mp hm).2.2
    change n / p = m / p at heq
    calc
      n = p * (n / p) := (Nat.mul_div_cancel' hnDvd).symm
      _ = p * (m / p) := by rw [heq]
      _ = m := Nat.mul_div_cancel' hmDvd
  · intro a ha
    refine ⟨p * a, lowOwnerFirstOwner_mul_mem_child_of_admitted hp ha, ?_⟩
    change (p * a) / p = a
    simpa [Nat.mul_comm] using Nat.mul_div_left a hp.pos
  · intro n hn
    have hnDvd := (Finset.mem_filter.mp hn).2.2
    rw [Nat.mul_div_cancel' hnDvd]

/-- Full phase-aligned physical cell, before removing the clipped exit. -/
def vf919CharacterAlignedCell
    (R p : ℕ) (sig : Finset ℕ) (chi : ℕ → ℂ) : ℂ :=
  (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
    vf919CharacterMobiusSite R chi a) +
    (chi p)⁻¹ * ∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig,
      vf919CharacterMobiusSite R chi n

/-- Native compensated interior with each complete parent phase preserved. -/
def vf919CharacterCompensatedInterior
    (R p : ℕ) (sig : Finset ℕ) (chi : ℕ → ℂ) : ℂ :=
  ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
    vf919ParentTwistedCompensatedSite R p chi a

/-- Literal unmatched p-child exit with original weights and phases. -/
def vf919CharacterClippedExit
    (R p : ℕ) (sig : Finset ℕ) (chi : ℕ → ℂ) : ℂ :=
  ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
    vf919CharacterMobiusSite R chi a

/-- **Signed physical reassembly first.** This is the entire actual cell,
including the clipped exit, not an energy of the compensated interior alone. -/
theorem vf919CharacterAlignedCell_eq_compensated_add_clipped
    {R p : ℕ} {sig : Finset ℕ} (chi : ℕ → ℂ) (hp : p.Prime)
    (hphase : chi p ≠ 0)
    (hmul : ∀ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
      chi (p * a) = chi p * chi a) :
    vf919CharacterAlignedCell R p sig chi =
      vf919CharacterCompensatedInterior R p sig chi +
        vf919CharacterClippedExit R p sig chi := by
  have hbase :
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
        vf919CharacterMobiusSite R chi a) =
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        vf919CharacterMobiusSite R chi a) +
      ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
        vf919CharacterMobiusSite R chi a := by
    unfold lowOwnerFirstOwnerAdmittedBaseFiber lowOwnerFirstOwnerClippedBaseFiber
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := lowOwnerFirstOwnerBaseFiber R p sig)
        (p := fun a => p * a ≤ squareRootEndpoint R)
        (f := vf919CharacterMobiusSite R chi)).symm
  have hinter :
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        vf919CharacterMobiusSite R chi a) +
      (chi p)⁻¹ * (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        vf919CharacterMobiusSite R chi (p * a)) =
      vf919CharacterCompensatedInterior R p sig chi := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    unfold vf919CharacterCompensatedInterior
    apply Finset.sum_congr rfl
    intro a ha
    exact vf919CharacterAlignedSite_eq_parentTwisted chi hp
      (lowOwnerFirstOwnerAdmittedBase_not_dvd ha) hphase (hmul a ha)
  unfold vf919CharacterAlignedCell vf919CharacterClippedExit
  rw [hbase, vf919FirstOwnerChild_sum_eq_returnedParents hp]
  rw [← hinter]
  ring

/-- Exact finite Hermitian Fubini; no absolute values are taken per site. -/
theorem vf919FiniteHermitianGram {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ a ∈ s, f a‖ ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, (f a * star (f b)).re := by
  have hn (z : ℂ) : ‖z‖ ^ 2 = (z * star z).re := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re] <;> ring
  rw [hn, star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [Complex.re_sum]

/-- The full parent phase kernel multiplies the EXISTING physical four-corner
mass. Opposite phases, zero phases, and all ordered cross terms are retained. -/
theorem vf919ParentTwistedCompensatedSite_hermitian_eq_fourCorner
    {R p a b : ℕ} (chi : ℕ → ℂ) (hp : p.Prime)
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    (vf919ParentTwistedCompensatedSite R p chi a *
        star (vf919ParentTwistedCompensatedSite R p chi b)).re =
      weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerZeroFrequencyMobiusWeight R) p a b *
        (chi a * star (chi b)).re := by
  calc
    _ = lowOwnerFirstOwnerCompensatedSite R p a *
        lowOwnerFirstOwnerCompensatedSite R p b *
        (chi a * star (chi b)).re := by
      simp [vf919ParentTwistedCompensatedSite, Complex.mul_re, Complex.mul_im] <;> ring
    _ = _ := by
      rw [lowOwnerFirstOwnerCompensatedSite_mul_eq_fourCornerMass hp ha hb]

/-- **Physical four-corner moment weld.** This is an exact equality on the
actual admitted-parent fibre, with the original native weights unchanged.
No OAI ideal-to-integer dictionary is assumed. -/
theorem vf919CharacterCompensatedInterior_norm_sq_eq_physicalGram
    {R p : ℕ} {sig : Finset ℕ} (chi : ℕ → ℂ) (hp : p.Prime) :
    ‖vf919CharacterCompensatedInterior R p sig chi‖ ^ 2 =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        ∑ b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
          weightedMoebiusFreshPrimeFourCornerMass
            (lowOwnerZeroFrequencyMobiusWeight R) p a b *
            (chi a * star (chi b)).re := by
  unfold vf919CharacterCompensatedInterior
  rw [vf919FiniteHermitianGram]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact vf919ParentTwistedCompensatedSite_hermitian_eq_fourCorner chi hp
    (lowOwnerFirstOwnerAdmittedBase_not_dvd ha)
    (lowOwnerFirstOwnerAdmittedBase_not_dvd hb)

/-- **Energy only after full reassembly.** The physical interior Gram is not
the full cell moment: its clipped square AND signed mixed term remain. -/
theorem vf919CharacterAlignedCell_norm_sq_eq_full_physicalGram
    {R p : ℕ} {sig : Finset ℕ} (chi : ℕ → ℂ) (hp : p.Prime)
    (hphase : chi p ≠ 0)
    (hmul : ∀ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
      chi (p * a) = chi p * chi a) :
    ‖vf919CharacterAlignedCell R p sig chi‖ ^ 2 =
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        ∑ b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
          weightedMoebiusFreshPrimeFourCornerMass
            (lowOwnerZeroFrequencyMobiusWeight R) p a b *
            (chi a * star (chi b)).re) +
      ‖vf919CharacterClippedExit R p sig chi‖ ^ 2 +
      2 * (vf919CharacterCompensatedInterior R p sig chi *
        star (vf919CharacterClippedExit R p sig chi)).re := by
  rw [vf919CharacterAlignedCell_eq_compensated_add_clipped chi hp hphase hmul]
  have hnorm (z w : ℂ) :
      ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * star w).re := by
    simpa only [Complex.sq_norm] using Complex.normSq_add z w
  rw [hnorm, vf919CharacterCompensatedInterior_norm_sq_eq_physicalGram chi hp]

/-- The native inverse phase at ONE is the already-compiled real compensated
cell, with its clipped exit. This identifies the exact untwisted specialization. -/
theorem vf919CharacterAlignedCell_one
    (R p : ℕ) (sig : Finset ℕ) :
    vf919CharacterAlignedCell R p sig (fun _ => 1) =
      ((lowOwnerFirstOwnerBaseAmplitude R p sig +
        lowOwnerFirstOwnerChildAmplitude R p sig : ℝ) : ℂ) := by
  simp [vf919CharacterAlignedCell, vf919CharacterMobiusSite,
    lowOwnerFirstOwnerBaseAmplitude, lowOwnerFirstOwnerChildAmplitude]

/-- Phase-faithful native realification of the ENTIRE physical cell moment. -/
theorem vf919CharacterAlignedCell_normalizedRealEnergy
    (R p : ℕ) (sig : Finset ℕ) (chi : ℕ → ℂ) :
    stableFarRealPairNormalizedEnergy
      (stableFarComplexToRealPair (vf919CharacterAlignedCell R p sig chi)) =
      ‖vf919CharacterAlignedCell R p sig chi‖ ^ 2 := by
  exact stableFarRealPairNormalizedEnergy_complexToRealPair _

/-- The signed projection plus anti-diagonal payment applies AFTER the full
cell, including the clipped exit, has been assembled. -/
theorem vf919CharacterAlignedCell_energy_eq_signed_plus_gap
    (R p : ℕ) (sig : Finset ℕ) (chi : ℕ → ℂ) :
    let v := stableFarComplexToRealPair (vf919CharacterAlignedCell R p sig chi)
    ‖vf919CharacterAlignedCell R p sig chi‖ ^ 2 =
      v.1 * v.2 + (v.1 - v.2) ^ 2 / 2 := by
  dsimp [stableFarComplexToRealPair]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

end RHLean.Proof

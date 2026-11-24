import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimePowerWeights
import RHLean.Analysis.AlpogeNativeSubgroupProjection
import RHLean.Analysis.NativePNTChebyshev

/-!
# The actual native source entering the local gain comparison

The reduced positive-site partner agrees with the physical partner on odd
inert prime powers. Its even steps are retained separately because the
first-return predicate in Alpoge's `g0` uses them as well. No equality of
the two partner maps on even exponents is asserted.

Signal-prime exclusions are empty. For every other prime, an excluded
atom is zero once `a / bTop <= p`, provided the SAME physical top widths
are at least `bTop`. The local comparison retains the remaining low
central-prime exclusion sum and pays the shift from `a` to `a - 2*c`
and from `w` to `w + c - heightShift` explicitly. The complete physical
ASK theorem below retains the ramified d-prime correction.

The accumulated logarithmic shift price is bounded by `6*c*nativePsi N`
using the existing exact prime-power census. After the original top/lift
sum and division by the original projection divisor it is at most
`12*c*nativePsi N / (b*Delta)`. The elementary native Chebyshev bound
also gives `12*(log 4+2)*c*N / (b*Delta)`. No assertion that this last
quantity fits a particular scale budget is made without the actual
parameter inequalities.

This is the arithmetic comparison needed before an actual lattice can
realize `g0`. It constructs no geometric gain, assumes no top-excess
bound, and does not prove the remaining mean rank-defect or global
height/norm estimate.

Source correspondence: Levent Alpoge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
(`partner`, `IsDist`, `Excl`, `g0`) and
`src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean`
(`not_excl_of_sg`, `excl_small_of_ge`, `hypothesis₂`). Only the finite
source comparison is reconstructed here, on the existing native host.
The source mirror states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis

private theorem localGain_odd_nsmul_bit (i : ℕ) (hi : Odd i) (z : ZMod 2) :
    i • z = z := by
  have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hi0 : (i : ZMod 2) ≠ 0 := by
    intro h
    have he : Even i := by rwa [ZMod.natCast_eq_zero_iff_even] at h
    exact (Nat.not_even_iff_odd.mpr hi) he
  have hi1 : (i : ZMod 2) = 1 := (hcase _).resolve_left hi0
  rw [nsmul_eq_mul, hi1, one_mul]

/-- The positive-site orbit used for local first returns. It is defined
from the actual Frobenius bits and displacement, including its even steps. -/
def alpogeNativeLocalGainPartner {H : Type*} [AddCommGroup H]
    (g : AlpogeNativeE0 × H) (t : H) (i : ℕ) : AlpogeNativeE0 × H :=
  ((0, i • (1 + g.1.2)), t + i • g.2)

/-- Only odd exponents of an inert Frobenius contribute to the source.
On precisely those exponents the reduced and physical partners agree. -/
theorem alpogeNativeLocalGainPartner_eq_partner_of_odd
    {H : Type*} [AddCommGroup H]
    (g : AlpogeNativeE0 × H) (t : H) (i : ℕ)
    (hg : ¬ alpogeNativeInPhi g) (hi : Odd i) :
    alpogeNativeLocalGainPartner g t i = alpogeNativePartner t (i • g) := by
  have hcase : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hg1 : g.1.1 = 1 := (hcase _).resolve_left hg
  apply Prod.ext
  · apply Prod.ext
    · change (0 : ZMod 2) = 1 + i • g.1.1 + 0
      rw [localGain_odd_nsmul_bit i hi, hg1]
      decide
    · change i • (1 + g.1.2) = 1 + i • g.1.2 + 0
      rw [localGain_odd_nsmul_bit i hi, localGain_odd_nsmul_bit i hi]
      simp
  · change t + i • g.2 = 0 + i • g.2 + t
    simp [add_comm]

/-- The original odd first return to a distinct top, expressed on the
reduced orbit. Oddness already implies that the return time is positive. -/
def alpogeNativeLocalGainExcluded {H : Type*} [AddCommGroup H]
    (TT : Finset H) (g : AlpogeNativeE0 × H) (t : H) (i : ℕ) : Prop :=
  Odd i ∧ ∃ s ∈ TT, s ≠ t ∧
    alpogeNativeLocalGainPartner g t i = alpogeNativeTopPl s ∧
    ∀ i' : ℕ, 0 < i' → i' < i →
      alpogeNativeLocalGainPartner g t i' ≠ alpogeNativeTopPl s

/-- At a signal Frobenius, every contributing odd partner has second
bit one, whereas a top has second bit zero. -/
theorem alpogeNativeLocalGain_not_excluded_of_signal
    {H : Type*} [AddCommGroup H]
    (TT : Finset H) (g : AlpogeNativeE0 × H) (t : H) (i : ℕ)
    (hSignal : g.1.2 = 0) :
    ¬ alpogeNativeLocalGainExcluded TT g t i := by
  rintro ⟨hi, s, _hs, _hst, hreturn, _hfirst⟩
  have hbit := congrArg (fun ρ : AlpogeNativeE0 × H => ρ.1.2) hreturn
  change i • (1 + g.1.2) = (0 : ZMod 2) at hbit
  rw [localGain_odd_nsmul_bit i hi, hSignal, add_zero] at hbit
  exact (by decide : (1 : ZMod 2) ≠ 0) hbit

namespace AlpogeThin

open Formalism.FrobeniusOrbits

/-- One atom of the existing physical odd-prime-power source. -/
def nativeDyadicLocalSourceAtom
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) (i : ℕ) : ℝ :=
  (alpogeNativeSiteCut a w t (p ^ i)
    (i • (alpogeNativeHostData e q d).frob p)).re

/-- The actual odd powers at one prime, before its `2 * log p` weight. -/
def nativeDyadicLocalOddSource
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 N).filter Odd,
    nativeDyadicLocalSourceAtom e q d p a t w i

/-- The actual atoms excluded by the local first-return rule. -/
def nativeDyadicLocalExcludedSource
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 N).filter Odd,
    if alpogeNativeLocalGainExcluded TT ((alpogeNativeHostData e q d).frob p) t i
    then nativeDyadicLocalSourceAtom e q d p a t w i else 0

/-- The retained local source after the original amplitude and width
shifts. This is a finite arithmetic sum, not a geometric gain field. -/
def nativeDyadicLocalRetainedSource
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a c heightShift : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 N).filter Odd,
    if alpogeNativeLocalGainExcluded TT ((alpogeNativeHostData e q d).frob p) t i
    then 0 else
      max ((a - 2 * c) / (p : ℝ) ^ i -
        (w (alpogeNativePartner t (i • (alpogeNativeHostData e q d).frob p)) +
          c - heightShift)) 0

/-- Actual active odd exponents: powers above the sharp source cutoff
have zero physical mass and incur no shift price. -/
def nativeDyadicLocalActivePowers (N p : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 N).filter Odd).filter (fun i => p ^ i ≤ N)

/-- Explicit price for the two shifts on active prime powers only. -/
def nativeDyadicLocalShiftCost (N p : ℕ) (c heightShift : ℝ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 N).filter Odd,
    if p ^ i ≤ N then (2 * c / (p : ℝ) ^ i + c - heightShift) else 0

/-- No first-return atom is lost at a signal prime. -/
theorem nativeDyadicLocalExcludedSource_eq_zero_of_signal
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hSignal : ((alpogeNativeHostData e q d).frob p).1.2 = 0) :
    nativeDyadicLocalExcludedSource e q d N p TT a t w = 0 := by
  unfold nativeDyadicLocalExcludedSource
  apply Finset.sum_eq_zero
  intro i _hi
  rw [ite_eq_right (alpogeNativeLocalGain_not_excluded_of_signal TT _ t i hSignal)]

/-- An excluded atom is already zero above the actual top-width cutoff.
Every original width and the physical prime-power location is retained. -/
theorem nativeDyadicLocalSourceAtom_eq_zero_of_excluded_high
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a bTop : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) (i : ℕ)
    (hp : p.Prime)
    (hInert : ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p))
    (hbTop : 0 < bTop)
    (hTop : ∀ s ∈ TT, bTop ≤ w (alpogeNativeTopPl s))
    (hHigh : a / bTop ≤ (p : ℝ))
    (hEx : alpogeNativeLocalGainExcluded TT ((alpogeNativeHostData e q d).frob p) t i) :
    nativeDyadicLocalSourceAtom e q d p a t w i = 0 := by
  obtain ⟨hi, s, hs, _hst, hreturn, _hfirst⟩ := hEx
  have hpartner : alpogeNativePartner t (i • (alpogeNativeHostData e q d).frob p) =
      alpogeNativeTopPl s :=
    (alpogeNativeLocalGainPartner_eq_partner_of_odd _ t i hInert hi).symm.trans hreturn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi0 : i ≠ 0 := Nat.ne_of_gt hi.pos
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ i := by
    exact_mod_cast Nat.le_self_pow hi0 p
  have ha : a ≤ bTop * (p : ℝ) := by
    have h := (div_le_iff₀ hbTop).mp hHigh
    nlinarith
  have hquot : a / (p : ℝ) ^ i ≤ w (alpogeNativeTopPl s) := by
    apply (div_le_iff₀ (pow_pos hp0 i)).mpr
    calc
      a ≤ bTop * (p : ℝ) := ha
      _ ≤ bTop * (p : ℝ) ^ i := mul_le_mul_of_nonneg_left hpow hbTop.le
      _ ≤ w (alpogeNativeTopPl s) * (p : ℝ) ^ i :=
        mul_le_mul_of_nonneg_right (hTop s hs) (pow_nonneg hp0.le i)
  simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re,
    Nat.cast_pow, hpartner, max_eq_right (sub_nonpos.mpr hquot)]

theorem nativeDyadicLocalExcludedSource_eq_zero_of_high
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a bTop : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hp : p.Prime)
    (hInert : ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p))
    (hbTop : 0 < bTop)
    (hTop : ∀ s ∈ TT, bTop ≤ w (alpogeNativeTopPl s))
    (hHigh : a / bTop ≤ (p : ℝ)) :
    nativeDyadicLocalExcludedSource e q d N p TT a t w = 0 := by
  unfold nativeDyadicLocalExcludedSource
  apply Finset.sum_eq_zero
  intro i _hi
  split_ifs with hEx
  · exact nativeDyadicLocalSourceAtom_eq_zero_of_excluded_high e q d p TT
      a bTop t w i hp hInert hbTop hTop hHigh hEx
  · rfl

/-- Only the unserved low central-prime exclusion sum remains. This is
the original excluded source, not an assumption that it is small. -/
def nativeDyadicLocalLowCentralRemainder
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a bTop : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) : ℝ :=
  if ((alpogeNativeHostData e q d).frob p).1.2 = 0 ∨ a / bTop ≤ (p : ℝ)
  then 0 else nativeDyadicLocalExcludedSource e q d N p TT a t w

theorem nativeDyadicLocalExcludedSource_eq_lowCentralRemainder
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a bTop : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hp : p.Prime)
    (hInert : ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p))
    (hbTop : 0 < bTop)
    (hTop : ∀ s ∈ TT, bTop ≤ w (alpogeNativeTopPl s)) :
    nativeDyadicLocalExcludedSource e q d N p TT a t w =
      nativeDyadicLocalLowCentralRemainder e q d N p TT a bTop t w := by
  unfold nativeDyadicLocalLowCentralRemainder
  split_ifs with h
  · rcases h with hSignal | hHigh
    · exact nativeDyadicLocalExcludedSource_eq_zero_of_signal e q d N p TT a t w hSignal
    · exact nativeDyadicLocalExcludedSource_eq_zero_of_high e q d N p TT
        a bTop t w hp hInert hbTop hTop hHigh
  · rfl

private theorem localGain_pos_part_shift (z price : ℝ) (hprice : 0 ≤ price) :
    max z 0 ≤ max (z - price) 0 + price := by
  apply max_le
  · have h := le_max_left (z - price) 0
    linarith
  · have h := le_max_right (z - price) 0
    linarith

/-- A quantitative comparison on the SAME local source and widths.
The excluded atoms remain explicit; the retained atoms undergo exactly
the amplitude and width shifts of the original baseline gain. -/
theorem nativeDyadicLocalOddSource_le_retained_add_excluded_add_shift
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a c heightShift : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hInert : ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p))
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ))
    (hc : 0 ≤ c) (hShift : heightShift ≤ c) :
    nativeDyadicLocalOddSource e q d N p a t w ≤
      nativeDyadicLocalRetainedSource e q d N p TT a c heightShift t w +
        nativeDyadicLocalExcludedSource e q d N p TT a t w +
          nativeDyadicLocalShiftCost N p c heightShift := by
  unfold nativeDyadicLocalOddSource nativeDyadicLocalRetainedSource
    nativeDyadicLocalExcludedSource nativeDyadicLocalShiftCost
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hActive : p ^ i ≤ N
  · simp only [ite_eq_left hActive]
    have hprice : 0 ≤ 2 * c / (p : ℝ) ^ i + c - heightShift := by
      have hdiv : 0 ≤ 2 * c / (p : ℝ) ^ i := by positivity
      linarith
    by_cases hEx : alpogeNativeLocalGainExcluded TT ((alpogeNativeHostData e q d).frob p) t i
    · simp only [ite_eq_left hEx, zero_add]
      linarith
    · simp only [ite_eq_right hEx, add_zero, nativeDyadicLocalSourceAtom,
        alpogeNativeSiteCut, Complex.ofReal_re, Nat.cast_pow]
      have h := localGain_pos_part_shift
        (a / (p : ℝ) ^ i -
          w (alpogeNativePartner t (i • (alpogeNativeHostData e q d).frob p)))
        (2 * c / (p : ℝ) ^ i + c - heightShift) hprice
      have heq : a / (p : ℝ) ^ i -
          w (alpogeNativePartner t (i • (alpogeNativeHostData e q d).frob p)) -
          (2 * c / (p : ℝ) ^ i + c - heightShift) =
        (a - 2 * c) / (p : ℝ) ^ i -
          (w (alpogeNativePartner t (i • (alpogeNativeHostData e q d).frob p)) +
            c - heightShift) := by ring
      rwa [heq] at h
  · have hiOdd : Odd i := (Finset.mem_filter.mp hi).2
    have hSite := alpogeNativeSiteCut_zero_above N (p ^ i) a t w hw hN
      (i • (alpogeNativeHostData e q d).frob p)
      ((nativeDyadic_not_inPhi_nsmul e _ i).mpr ⟨hiOdd, hInert⟩)
      (Nat.lt_of_not_ge hActive)
    have hzero : nativeDyadicLocalSourceAtom e q d p a t w i = 0 := by
      unfold nativeDyadicLocalSourceAtom
      rw [hSite]
      rfl
    simp only [ite_eq_right hActive, hzero, add_zero]
    split_ifs <;> positivity

/-- The number of actual active exponents is logarithmic in the sharp
source cutoff; it is not the global integer cutoff `N`. -/
theorem nativeDyadicLocalActivePowers_card_le_log
    (N p : ℕ) (hp : p.Prime) :
    (nativeDyadicLocalActivePowers N p).card ≤ Nat.log p N := by
  have hsub : nativeDyadicLocalActivePowers N p ⊆ Finset.Icc 1 (Nat.log p N) := by
    intro i hi
    change i ∈ ((Finset.Icc 1 N).filter Odd).filter (fun j => p ^ j ≤ N) at hi
    obtain ⟨hiOdd, hpow⟩ := Finset.mem_filter.mp hi
    have hiRange := (Finset.mem_filter.mp hiOdd).1
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hiRange).1,
      Nat.le_log_of_pow_le hp.one_lt hpow⟩
  have h := Finset.card_le_card hsub
  simpa [Nat.card_Icc] using h

/-- An explicit logarithmic bound for the shift cost. No cancellation
or arithmetic signed-source bound is used. -/
theorem nativeDyadicLocalShiftCost_le
    (N p : ℕ) (c heightShift : ℝ)
    (hp : p.Prime) (hc : 0 ≤ c) (hShift : 0 ≤ heightShift) :
    nativeDyadicLocalShiftCost N p c heightShift ≤ 3 * c * (Nat.log p N : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hterm : ∀ i : ℕ, 2 * c / (p : ℝ) ^ i + c - heightShift ≤ 3 * c := by
    intro i
    have hdiv : 2 * c / (p : ℝ) ^ i ≤ 2 * c :=
      div_le_self (by positivity) (one_le_pow₀ hp1)
    linarith
  have hcard : ((nativeDyadicLocalActivePowers N p).card : ℝ) ≤ Nat.log p N := by
    exact_mod_cast nativeDyadicLocalActivePowers_card_le_log N p hp
  have hsum : nativeDyadicLocalShiftCost N p c heightShift =
      ∑ i ∈ nativeDyadicLocalActivePowers N p,
        (2 * c / (p : ℝ) ^ i + c - heightShift) := by
    unfold nativeDyadicLocalShiftCost nativeDyadicLocalActivePowers
    simp only [Finset.sum_filter]
  rw [hsum]
  calc
    (∑ i ∈ nativeDyadicLocalActivePowers N p,
        (2 * c / (p : ℝ) ^ i + c - heightShift)) ≤
        ∑ _i ∈ nativeDyadicLocalActivePowers N p, (3 * c) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((nativeDyadicLocalActivePowers N p).card : ℝ) * (3 * c) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.log p N : ℝ) * (3 * c) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 3 * c * (Nat.log p N : ℝ) := by ring

/-- The local comparison with the vanishing exclusions discharged. The
remaining term is exactly the low central-prime source. -/
theorem nativeDyadicLocalOddSource_le_retained_add_lowCentral
    (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e))
    (a bTop c heightShift : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hp : p.Prime)
    (hInert : ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p))
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ))
    (hbTop : 0 < bTop)
    (hTop : ∀ s ∈ TT, bTop ≤ w (alpogeNativeTopPl s))
    (hc : 0 ≤ c) (hShift : 0 ≤ heightShift ∧ heightShift ≤ c) :
    nativeDyadicLocalOddSource e q d N p a t w ≤
      nativeDyadicLocalRetainedSource e q d N p TT a c heightShift t w +
        nativeDyadicLocalLowCentralRemainder e q d N p TT a bTop t w +
          3 * c * (Nat.log p N : ℝ) := by
  have h := nativeDyadicLocalOddSource_le_retained_add_excluded_add_shift
    e q d N p TT a c heightShift t w hInert hw hN hc hShift.2
  rw [nativeDyadicLocalExcludedSource_eq_lowCentralRemainder e q d N p TT
    a bTop t w hp hInert hbTop hTop] at h
  exact h.trans (add_le_add le_rfl
    (nativeDyadicLocalShiftCost_le N p c heightShift hp hc hShift.1))

/-- Exact identification with the existing native odd-class ASK. -/
theorem nativeDyadicOddClassASK_re_eq_localSource
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    (nativeDyadicOddClassASK e q d N a t w).re =
      ∑ p ∈ nativeDyadicInertPrimes e q d N,
        (2 * Real.log p) * nativeDyadicLocalOddSource e q d N p a t w := by
  simp [nativeDyadicOddClassASK, nativeDyadicLocalOddSource,
    nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.mul_re,
    Complex.log_re, Finset.mul_sum]

/-- The complete original physical ASK, with all d powers retained,
is controlled by the shifted retained source, its explicit low central
remainder, and the proved finite shift price. -/
theorem nativeDyadicFullASK_re_le_localRetainedSource
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (TT : Finset (AlpogeNativeDyadicH e))
    (a bTop c heightShift : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ))
    (hbTop : 0 < bTop)
    (hTop : ∀ s ∈ TT, bTop ≤ w (alpogeNativeTopPl s))
    (hc : 0 ≤ c) (hShift : 0 ≤ heightShift ∧ heightShift ≤ c) :
    (alpogeNativeFullKernelASK (alpogeNativeHostData e q d).inertia
      (alpogeNativeHostData e q d).frob N a t w).re ≤
      (∑ p ∈ nativeDyadicInertPrimes e q d N, (2 * Real.log p) *
        (nativeDyadicLocalRetainedSource e q d N p TT a c heightShift t w +
          nativeDyadicLocalLowCentralRemainder e q d N p TT a bTop t w +
            3 * c * (Nat.log p N : ℝ))) +
        (nativeDyadicDPrimeASK e q d N a t w).re := by
  rw [nativeDyadicHost_fullASK_eq_oddClassSums_add_dCorrection
    e q d N hH a t w hw hN, Complex.add_re,
    nativeDyadicOddClassASK_re_eq_localSource]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro p hpMem
  change p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter
    (fun r => ¬ r ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) r = -1) at hpMem
  obtain ⟨hpBase, hpN, hpJac⟩ := Finset.mem_filter.mp hpMem
  have hp : p.Prime := (Finset.mem_filter.mp hpBase).2
  have hInert : ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p) :=
    (nativeDyadicHostData_frob_not_inPhi_iff e q d p hH hp hpN).mpr hpJac
  exact mul_le_mul_of_nonneg_left
    (nativeDyadicLocalOddSource_le_retained_add_lowCentral e q d N p TT
      a bTop c heightShift t w hp hInert hw hN hbTop hTop hc hShift)
    (mul_nonneg (by norm_num) (Real.log_natCast_nonneg p))

/-- The comparison reaches the original signed source with the same
principal correction. No absolute value or separate bound replaces MAIN,
and every ramified d-prime atom remains on the right-hand side. -/
theorem nativeDyadicDe_re_le_localRetainedSource
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (TT : Finset (AlpogeNativeDyadicH e))
    (ell : AddChar (AlpogeNativeE0 × AlpogeNativeDyadicH e) ℂ → ℂ)
    (a bTop c heightShift : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ))
    (hbTop : 0 < bTop)
    (hTop : ∀ s ∈ TT, bTop ≤ w (alpogeNativeTopPl s))
    (hc : 0 ≤ c) (hShift : 0 ≤ heightShift ∧ heightShift ≤ c) :
    (alpogeNativeDe (alpogeNativeHostData e q d).inertia
      (alpogeNativeHostData e q d).frob ell a t w).re ≤
      (∑ p ∈ nativeDyadicInertPrimes e q d N, (2 * Real.log p) *
        (nativeDyadicLocalRetainedSource e q d N p TT a c heightShift t w +
          nativeDyadicLocalLowCentralRemainder e q d N p TT a bTop t w +
            3 * c * (Nat.log p N : ℝ))) +
        (nativeDyadicDPrimeASK e q d N a t w).re -
          (alpogeNativeMAIN ell a w).re := by
  rw [← alpogeNativeConcreteHostASK_sub_MAIN_eq_De e q d ell N a t w ha hw hN,
    Complex.sub_re]
  exact sub_le_sub_right
    (nativeDyadicFullASK_re_le_localRetainedSource e q d N hH TT a bTop c
      heightShift t w hw hN hbTop hTop hc hShift) _

/-- The actual unramified inert primes form a subset of the existing
native prime-coordinate set, with the same integer endpoint. -/
theorem nativeDyadicInertPrimes_subset_nativePrimeSet (e q d N : ℕ) :
    nativeDyadicInertPrimes e q d N ⊆ nativePrimeSet N := by
  intro p hp
  change p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter
    (fun r => ¬ r ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) r = -1) at hp
  obtain ⟨hpBase, _hpClass⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.mp hpBase
  change p ∈ (Finset.Icc 1 N).filter Nat.Prime
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hpPrime.one_le, Nat.lt_succ_iff.mp (Finset.mem_range.mp hpRange)⟩, hpPrime⟩

/-- The logarithmic exponent multiplicity is bounded by the SAME native
von Mangoldt mass, by its existing exact prime-power decomposition. -/
theorem nativeDyadicInertLogMultiplicity_le_nativePsi (e q d N : ℕ) :
    (∑ p ∈ nativeDyadicInertPrimes e q d N,
      Real.log p * (Nat.log p N : ℝ)) ≤ nativePsi N := by
  rw [nativePsi_eq_sum_mul_log_prime]
  calc
    (∑ p ∈ nativeDyadicInertPrimes e q d N,
        Real.log p * (Nat.log p N : ℝ)) =
        ∑ p ∈ nativeDyadicInertPrimes e q d N,
          (Nat.log p N : ℝ) * Real.log p := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact mul_comm _ _
    _ ≤ ∑ p ∈ nativePrimeSet N, (Nat.log p N : ℝ) * Real.log p :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (nativeDyadicInertPrimes_subset_nativePrimeSet e q d N)
        (fun p _hp _hnot =>
          mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))

/-- The precise accumulated shift price in the complete-source theorem
is at most `6*c*psi(N)`; the prime-power count is not bounded one prime
at a time by `log N`. -/
theorem nativeDyadicLocalLogShiftPrice_le_nativePsi
    (e q d N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ p ∈ nativeDyadicInertPrimes e q d N,
      (2 * Real.log p) * (3 * c * (Nat.log p N : ℝ))) ≤
        6 * c * nativePsi N := by
  calc
    (∑ p ∈ nativeDyadicInertPrimes e q d N,
        (2 * Real.log p) * (3 * c * (Nat.log p N : ℝ))) =
        (6 * c) * ∑ p ∈ nativeDyadicInertPrimes e q d N,
          Real.log p * (Nat.log p N : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ 6 * c * nativePsi N :=
      mul_le_mul_of_nonneg_left
        (nativeDyadicInertLogMultiplicity_le_nativePsi e q d N) (by positivity)

/-- The unrounded shift sum itself satisfies the same prime-power
budget whenever the original height shift is nonnegative. -/
theorem nativeDyadicLocalShiftCost_sum_le_nativePsi
    (e q d N : ℕ) (c heightShift : ℝ)
    (hc : 0 ≤ c) (hShift : 0 ≤ heightShift) :
    (∑ p ∈ nativeDyadicInertPrimes e q d N,
      (2 * Real.log p) * nativeDyadicLocalShiftCost N p c heightShift) ≤
        6 * c * nativePsi N := by
  calc
    (∑ p ∈ nativeDyadicInertPrimes e q d N,
        (2 * Real.log p) * nativeDyadicLocalShiftCost N p c heightShift) ≤
        ∑ p ∈ nativeDyadicInertPrimes e q d N,
          (2 * Real.log p) * (3 * c * (Nat.log p N : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime :=
        (Finset.mem_filter.mp
          (nativeDyadicInertPrimes_subset_nativePrimeSet e q d N hp)).2
      exact mul_le_mul_of_nonneg_left
        (nativeDyadicLocalShiftCost_le N p c heightShift hpPrime hc hShift)
        (mul_nonneg (by norm_num) (Real.log_natCast_nonneg p))
    _ ≤ 6 * c * nativePsi N := nativeDyadicLocalLogShiftPrice_le_nativePsi e q d N c hc

/-- Summing the proved shift price over the original tops and lifts,
then dividing by the actual projection divisor, cancels exactly those
two multiplicities. The density is the existing native density of T2. -/
theorem nativeDyadicLocalLogShiftPrice_normalized_le_nativePsi
    (e q d N m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e))
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (b c : ℝ) (hb : 0 < b) (hc : 0 ≤ c) :
    (∑ _t ∈ TT, ∑ _j : Fin m,
      ∑ p ∈ nativeDyadicInertPrimes e q d N,
        (2 * Real.log p) * (3 * c * (Nat.log p N : ℝ))) /
        alpogeNativeProjectionDivisor TT T2 m b ≤
      12 * c * nativePsi N / (b * alpogeNativeProjectionDensity T2) := by
  have hSum :
      (∑ _t ∈ TT, ∑ _j : Fin m,
        ∑ p ∈ nativeDyadicInertPrimes e q d N,
          (2 * Real.log p) * (3 * c * (Nat.log p N : ℝ))) ≤
        (TT.card : ℝ) * (m : ℝ) * (6 * c * nativePsi N) := by
    calc
      _ = (TT.card : ℝ) * (m : ℝ) *
          (∑ p ∈ nativeDyadicInertPrimes e q d N,
            (2 * Real.log p) * (3 * c * (Nat.log p N : ℝ))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]
      _ ≤ (TT.card : ℝ) * (m : ℝ) * (6 * c * nativePsi N) :=
        mul_le_mul_of_nonneg_left
          (nativeDyadicLocalLogShiftPrice_le_nativePsi e q d N c hc) (by positivity)
  have hQ := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm b hb
  have ht : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hDelta : 0 < alpogeNativeProjectionDensity T2 := by
    unfold alpogeNativeProjectionDensity
    exact div_pos (by exact_mod_cast hT2.card_pos)
      (by exact_mod_cast Fintype.card_pos)
  refine (div_le_div_of_nonneg_right hSum hQ.le).trans_eq ?_
  unfold alpogeNativeProjectionDivisor
  field_simp [ht.ne', hm'.ne', hb.ne', hDelta.ne']
  ring

/-- The existing elementary native Chebyshev bound makes the normalized
shift price explicit in N. This uses no prime-distribution asymptotic. -/
theorem nativeDyadicLocalLogShiftPrice_normalized_le
    (e q d N m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e))
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (b c : ℝ) (hb : 0 < b) (hc : 0 ≤ c) :
    (∑ _t ∈ TT, ∑ _j : Fin m,
      ∑ p ∈ nativeDyadicInertPrimes e q d N,
        (2 * Real.log p) * (3 * c * (Nat.log p N : ℝ))) /
        alpogeNativeProjectionDivisor TT T2 m b ≤
      12 * (Real.log 4 + 2) * c * (N : ℝ) /
        (b * alpogeNativeProjectionDensity T2) := by
  apply (nativeDyadicLocalLogShiftPrice_normalized_le_nativePsi
    e q d N m TT T2 hTT hT2 hm b c hb hc).trans
  apply div_le_div_of_nonneg_right _
    (by unfold alpogeNativeProjectionDensity; positivity)
  calc
    12 * c * nativePsi N ≤ 12 * c * ((Real.log 4 + 2) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (nativePsi_le_const_mul N) (by positivity)
    _ = 12 * (Real.log 4 + 2) * c * (N : ℝ) := by ring

end AlpogeThin
end RHLean.Analysis

end

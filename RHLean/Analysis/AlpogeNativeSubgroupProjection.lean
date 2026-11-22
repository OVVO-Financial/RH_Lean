import Mathlib
import RHLean.Analysis.AlpogeNativeSharpASKBalance

/-!
# Native subgroup projection and the earned thick-source divisor

The finite character calculation is rebuilt over the exact native two-bit
host.  The subgroup average, the multiplicity count and the thick density
produce the factor |TT| * m * b * (|T2| / |H|) / 2.  It is not an assigned
geometric multiplicity.  An arbitrary finite set of retained characters is
allowed; the complete excluded-character norm correction is paid explicitly.

The physical attachment below retains the original prime powers, inertia,
Frobenius phases and all site-dependent widths.  The non-thick source and
the signed thick-width displacement remain literal finite sums.  No bound
on those sums, lattice witness or RH-strength estimate is assumed.

Blueprint: CocoSgt/riemann-hypothesis-lean at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean.
-/

noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis

section FiniteProjection

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The original first-bit colour, with its actual host coordinate. -/
def alpogeNativeProjectionE1 (h : H) : AlpogeNativeE0 × H := ((1, 0), h)

/-- Characters trivial on the actual subgroup of host translations. -/
def alpogeNativeProjectionChars (A0 : AddSubgroup H) :
    Finset (AddChar (AlpogeNativeE0 × H) ℂ) := by
  classical
  exact Finset.univ.filter (fun ψ => ∀ s ∈ A0, ψ (0, s) = 1)

omit [DecidableEq H] in
theorem alpogeNativeProjectionChars_mem (A0 : AddSubgroup H)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) :
    ψ ∈ alpogeNativeProjectionChars A0 ↔ ∀ s ∈ A0, ψ (0, s) = 1 := by
  classical
  simp [alpogeNativeProjectionChars]

/-- The denominator is exactly twice the original host size. -/
theorem alpogeNativeProjectionPhi_card :
    (alpogeNativePhiSet H).card = 2 * Fintype.card H := by
  classical
  have hset : alpogeNativePhiSet H =
      ((Finset.univ : Finset AlpogeNativeE0).filter (fun e => e.1 = 0)) ×ˢ
        (Finset.univ : Finset H) := by
    ext ρ
    simp [alpogeNativePhiSet, alpogeNativeInPhi]
  have htwo : ((Finset.univ : Finset AlpogeNativeE0).filter
      (fun e => e.1 = 0)).card = 2 := by decide
  rw [hset, Finset.card_product, htwo, Finset.card_univ]

/-- Exact annihilator projection.  The translate s must belong to the
same subgroup over which the character is averaged. -/
theorem alpogeNativeProjection_sum_phase (A0 : AddSubgroup H)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (s t : H) (hs : s ∈ A0) :
    (∑ u : A0, ψ (-(alpogeNativeProjectionE1 (s + (u : H) - t)))) =
      if ψ ∈ alpogeNativeProjectionChars A0 then
        (Fintype.card A0 : ℂ) * ψ (alpogeNativeProjectionE1 t) else 0 := by
  classical
  have hg : ∀ u : A0,
      -(alpogeNativeProjectionE1 (s + (u : H) - t)) =
        alpogeNativeProjectionE1 t + (0, -s) + (0, -(u : H)) := by
    intro u
    ext
    · norm_num [alpogeNativeProjectionE1, AlpogeNativeE0]
    · simp [alpogeNativeProjectionE1]
    · simp [alpogeNativeProjectionE1]
      abel
  simp_rw [hg, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum]
  split_ifs with h
  · have h' := (alpogeNativeProjectionChars_mem A0 ψ).1 h
    rw [h' _ (A0.neg_mem hs),
      Finset.sum_congr rfl (fun (u : A0) _ => h' _ (A0.neg_mem u.2))]
    simp [mul_comm]
  · let χ : AddChar A0 ℂ :=
      ψ.compAddMonoidHom ((AddMonoidHom.inr AlpogeNativeE0 H).comp A0.subtype)
    have hχ : ∀ u : A0, χ u = ψ (0, (u : H)) := fun _ => rfl
    have hne : χ ≠ 0 := by
      intro hzero
      apply h
      rw [alpogeNativeProjectionChars_mem]
      intro v hv
      rw [← hχ ⟨v, hv⟩, hzero, AddChar.zero_apply]
    have hsum := AddChar.sum_eq_zero_iff_ne_zero.2 hne
    have hneg : (∑ u : A0, ψ (0, -(u : H))) = ∑ u : A0, χ u := by
      rw [← Equiv.sum_comp (Equiv.neg A0) χ]
      rfl
    rw [hneg, hsum, mul_zero]

/-- Density of the genuine selected host sites. -/
def alpogeNativeProjectionDensity (T2 : Finset H) : ℝ :=
  (T2.card : ℝ) / (Fintype.card H : ℝ)

/-- Frozen thick part, with the original two-bit Fourier normalization.
The response F can subsequently be instantiated by the complete native GPsi. -/
def alpogeNativeFrozenThick
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (b y : ℝ) (u t : H) : ℂ :=
  (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ s ∈ T2, ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
      ψ (-(alpogeNativeProjectionE1 (s + u - t))) * ((b : ℂ) * F ψ y)

/-- Subgroup averaging earns b * density / 2 before any source estimate. -/
theorem alpogeNativeFrozenThick_sum_subgroup
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (hT2 : ∀ s ∈ T2, s ∈ A0)
    (b y : ℝ) (t : H) :
    (∑ u : A0, alpogeNativeFrozenThick F T2 b y u t) =
      (((Fintype.card A0 : ℝ) * (b * (alpogeNativeProjectionDensity T2 / 2)) : ℝ) : ℂ) *
        ∑ ψ ∈ alpogeNativeProjectionChars A0,
          ψ (alpogeNativeProjectionE1 t) * F ψ y := by
  classical
  unfold alpogeNativeFrozenThick
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hin : ∀ s ∈ T2,
      (∑ u : A0, ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        ψ (-(alpogeNativeProjectionE1 (s + (u : H) - t))) * ((b : ℂ) * F ψ y)) =
      ((Fintype.card A0 : ℂ) * b) *
        ∑ ψ ∈ alpogeNativeProjectionChars A0,
          ψ (alpogeNativeProjectionE1 t) * F ψ y := by
    intro s hs
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,
      alpogeNativeProjection_sum_phase A0 _ s t (hT2 s hs), ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ψ _ => by ring)
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul,
    alpogeNativeProjectionPhi_card]
  have hn : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold alpogeNativeProjectionDensity
  push_cast
  field_simp [hn]
  <;> ring

/-- All annihilator characters at all original top heights; no height is
silently replaced by a common reference. -/
def alpogeNativeProjectedSignal
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (TT : Finset H) (a : H → ℝ) (b : ℝ) : ℝ :=
  (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
    (∑ ψ ∈ alpogeNativeProjectionChars A0,
      ψ (alpogeNativeProjectionE1 t) * F ψ (a t / b)).re

/-- The original finite divisor, before any scale comparison. -/
def alpogeNativeProjectionDivisor
    (TT T2 : Finset H) (m : ℕ) (b : ℝ) : ℝ :=
  (TT.card : ℝ) * m * b * alpogeNativeProjectionDensity T2 / 2

omit [DecidableEq H] in
theorem alpogeNativeProjectionDivisor_pos
    (TT T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty)
    (m : ℕ) (hm : 0 < m) (b : ℝ) (hb : 0 < b) :
    0 < alpogeNativeProjectionDivisor TT T2 m b := by
  have ht : (0 : ℝ) < TT.card := by exact_mod_cast Finset.card_pos.mpr hTT
  have hs : (0 : ℝ) < T2.card := by exact_mod_cast Finset.card_pos.mpr hT2
  have hn : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  unfold alpogeNativeProjectionDivisor alpogeNativeProjectionDensity
  positivity

/-- The complete finite average equals its earned signal coefficient.
The multiplicity m comes from the actual Fin m sum. -/
theorem alpogeNativeFrozenThick_average_eq_signal
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (TT T2 : Finset H) (hTT : TT.Nonempty)
    (hT2 : ∀ s ∈ T2, s ∈ A0)
    (m : ℕ) (a : H → ℝ) (b : ℝ) :
    (1 / (Fintype.card A0 : ℝ)) *
      ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m,
        (alpogeNativeFrozenThick F T2 b (a t / b) u t).re =
      alpogeNativeProjectionDivisor TT T2 m b *
        alpogeNativeProjectedSignal A0 F TT a b := by
  classical
  have ht : (TT.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hTT).ne'
  have hu : (Fintype.card A0 : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m,
      (alpogeNativeFrozenThick F T2 b (a t / b) u t).re) =
      (Fintype.card A0 : ℝ) * (m * b * (alpogeNativeProjectionDensity T2 / 2)) *
        ∑ t ∈ TT, (∑ ψ ∈ alpogeNativeProjectionChars A0,
          ψ (alpogeNativeProjectionE1 t) * F ψ (a t / b)).re := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.mul_sum, ← Complex.re_sum,
      alpogeNativeFrozenThick_sum_subgroup A0 F T2 hT2 b (a t / b) t,
      Complex.re_ofReal_mul]
    ring
  rw [hs]
  unfold alpogeNativeProjectionDivisor alpogeNativeProjectedSignal
  field_simp [ht, hu]
  <;> ring

/-- Retained characters keep their original phases and heights. -/
def alpogeNativeRetainedSignal
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (Kp : Finset (AddChar (AlpogeNativeE0 × H) ℂ))
    (TT : Finset H) (a : H → ℝ) (b : ℝ) : ℝ :=
  (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
    ∑ ψ ∈ Kp, (ψ (alpogeNativeProjectionE1 t) * F ψ (a t / b)).re

/-- The entire excluded-character correction, with no discarded conductor
or exceptional character.  It is not declared to have root size. -/
def alpogeNativeExcludedCharacterMass
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (Kp : Finset (AddChar (AlpogeNativeE0 × H) ℂ))
    (TT : Finset H) (a : H → ℝ) (b : ℝ) : ℝ :=
  (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
    ∑ ψ ∈ alpogeNativeProjectionChars A0 \ Kp, ‖F ψ (a t / b)‖

/-- A paid finite one-sided character inequality.  Only the excluded
characters are charged by their norms; retained signed phases survive. -/
omit [DecidableEq H] in
theorem alpogeNativeRetained_sub_excluded_le_projected
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (Kp : Finset (AddChar (AlpogeNativeE0 × H) ℂ))
    (hKp : Kp ⊆ alpogeNativeProjectionChars A0)
    (TT : Finset H) (a : H → ℝ) (b : ℝ) :
    alpogeNativeRetainedSignal F Kp TT a b -
        alpogeNativeExcludedCharacterMass A0 F Kp TT a b ≤
      alpogeNativeProjectedSignal A0 F TT a b := by
  classical
  unfold alpogeNativeRetainedSignal alpogeNativeExcludedCharacterMass
    alpogeNativeProjectedSignal
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro t _ht
  rw [Complex.re_sum, ← Finset.sum_sdiff hKp]
  have hlow : -(∑ ψ ∈ alpogeNativeProjectionChars A0 \ Kp,
      ‖F ψ (a t / b)‖) ≤
      ∑ ψ ∈ alpogeNativeProjectionChars A0 \ Kp,
        (ψ (alpogeNativeProjectionE1 t) * F ψ (a t / b)).re := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ψ _hψ
    have hn : ‖ψ (alpogeNativeProjectionE1 t) * F ψ (a t / b)‖ =
        ‖F ψ (a t / b)‖ := by
      rw [norm_mul, AddChar.norm_apply, one_mul]
    have h := (abs_le.1 (Complex.abs_re_le_norm
      (ψ (alpogeNativeProjectionE1 t) * F ψ (a t / b)))).1
    rwa [hn] at h
  linarith

end FiniteProjection

section PhysicalAttachment

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The selected colours are actual translates of T2 in the first-bit
coset.  Their partners are ((0,1),s+u), not invented sign labels. -/
def alpogeNativeProjectionThickColours (T2 : Finset H) (u t : H) :
    Finset (AlpogeNativeE0 × H) :=
  T2.image (fun s => alpogeNativeProjectionE1 (s + u - t))

theorem alpogeNativeProjectionThick_partner (s u t : H) :
    alpogeNativePartner t (alpogeNativeProjectionE1 (s + u - t)) =
      (((0, 1) : AlpogeNativeE0), s + u) := by
  ext
  · norm_num [alpogeNativePartner, alpogeNativeCconj, alpogeNativeTopPl,
      alpogeNativeProjectionE1, AlpogeNativeE0]
  · simp [alpogeNativePartner, alpogeNativeCconj, alpogeNativeTopPl,
      alpogeNativeProjectionE1]
  · simp [alpogeNativePartner, alpogeNativeCconj, alpogeNativeTopPl,
      alpogeNativeProjectionE1]

theorem alpogeNativeProjectionThickColours_subset (T2 : Finset H) (u t : H) :
    alpogeNativeProjectionThickColours T2 u t ⊆
      Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g) := by
  classical
  intro g hg
  obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp hg
  norm_num [Finset.mem_filter, alpogeNativeProjectionE1, alpogeNativeInPhi,
    AlpogeNativeE0]

/-- An original colour contribution, including every character and its
own width-shifted response. -/
def alpogeNativeProjectionColourTerm
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (g : AlpogeNativeE0 × H) : ℂ :=
  ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
    ψ (-g) * ((w (alpogeNativePartner t g) : ℂ) *
      F ψ (a / w (alpogeNativePartner t g)))

/-- The native complete De expression, with an arbitrary response family.
The arithmetic specialization below is proved equal to alpogeNativeDe. -/
def alpogeNativeProjectionFullSource
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) : ℂ :=
  (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ g ∈ Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
      alpogeNativeProjectionColourTerm F a t w g

/-- Literal thick contribution at the original, site-dependent widths. -/
def alpogeNativeProjectionActualThick
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) : ℂ :=
  (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ s ∈ T2, alpogeNativeProjectionColourTerm F a t w
      (alpogeNativeProjectionE1 (s + u - t))

/-- All complementary colours at their ORIGINAL widths.  This is an
explicit finite complement, not a symbol assumed to be small. -/
def alpogeNativeProjectionThinReturn
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) : ℂ :=
  (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ g ∈ (Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
        alpogeNativeProjectionThickColours T2 u t,
      alpogeNativeProjectionColourTerm F a t w g

/-- Signed thick-width displacement.  It is retained jointly with the
complementary source, so no characterwise or positive-part loss occurs. -/
def alpogeNativeProjectionWidthReturn
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a b : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) : ℂ :=
  alpogeNativeProjectionActualThick F T2 a u t w -
    alpogeNativeFrozenThick F T2 b (a / b) u t

theorem alpogeNativeProjectionFull_eq_thick_add_thin
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeProjectionFullSource F a t w =
      alpogeNativeProjectionActualThick F T2 a u t w +
        alpogeNativeProjectionThinReturn F T2 a u t w := by
  classical
  have hinj : Function.Injective
      (fun s : H => alpogeNativeProjectionE1 (s + u - t)) := by
    intro s s' h
    have h' : s + u - t = s' + u - t := congrArg Prod.snd h
    have h'' : s + u = s' + u := by
      simpa only [sub_add_cancel] using congrArg (fun x : H => x + t) h'
    exact add_right_cancel h''
  have hsum : (∑ g ∈ alpogeNativeProjectionThickColours T2 u t,
      alpogeNativeProjectionColourTerm F a t w g) =
      ∑ s ∈ T2, alpogeNativeProjectionColourTerm F a t w
        (alpogeNativeProjectionE1 (s + u - t)) := by
    unfold alpogeNativeProjectionThickColours
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => hinj h
  unfold alpogeNativeProjectionFullSource alpogeNativeProjectionActualThick
    alpogeNativeProjectionThinReturn
  rw [← Finset.sum_sdiff (alpogeNativeProjectionThickColours_subset T2 u t), hsum]
  ring

/-- Exact source split suitable for the separately constructed geometric
width witness.  Neither remainder has been discarded or bounded. -/
theorem alpogeNativeProjectionFull_eq_frozen_add_returns
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a b : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeProjectionFullSource F a t w =
      alpogeNativeFrozenThick F T2 b (a / b) u t +
        (alpogeNativeProjectionWidthReturn F T2 a b u t w +
          alpogeNativeProjectionThinReturn F T2 a u t w) := by
  rw [alpogeNativeProjectionFull_eq_thick_add_thin F T2 a u t w]
  unfold alpogeNativeProjectionWidthReturn
  ring

theorem alpogeNativeProjectionFullSource_eq_nativeDe
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeProjectionFullSource
      (alpogeNativeFrobInertiaGPsi inertia frob ell) a t w =
      alpogeNativeDe inertia frob ell a t w := by
  classical
  unfold alpogeNativeProjectionFullSource alpogeNativeProjectionColourTerm
    alpogeNativeDe
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  apply Finset.sum_congr rfl
  intro ψ _hψ
  rw [AddChar.map_neg_eq_conj]
  ring

/-- The ORIGINAL physical ASK-MAIN averaged over one genuine subgroup.
The height remains a_t and the width remains w(u,j,rho) throughout. -/
def alpogeNativePhysicalSubgroupTopExcess
    (A0 : AddSubgroup H)
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card A0 : ℝ)) * ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
    (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j) -
      alpogeNativeMAIN ell (a t) (w u j)).re

/-- One signed remainder on the same complete physical data.  A geometric
width theorem can be applied here without discarding its favorable terms. -/
def alpogeNativeProjectionSignedRemainder
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (TT T2 : Finset H) {m : ℕ} (a : H → ℝ) (b : ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card A0 : ℝ)) * ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
    (alpogeNativeProjectionWidthReturn F T2 (a t) b u t (w u j) +
      alpogeNativeProjectionThinReturn F T2 (a t) u t (w u j)).re

/-- Complete native ASK-MAIN = earned character signal + original signed
return.  All characters, prime powers, inertia and widths are retained. -/
theorem alpogeNativePhysicalSubgroup_eq_projected_add_remainder
    (A0 : AddSubgroup H)
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT T2 : Finset H) (hTT : TT.Nonempty)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (a : H → ℝ) (b : ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ)) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w =
      alpogeNativeProjectionDivisor TT T2 m b *
        alpogeNativeProjectedSignal A0 (alpogeNativeFrobInertiaGPsi inertia frob ell) TT a b +
      alpogeNativeProjectionSignedRemainder A0
        (alpogeNativeFrobInertiaGPsi inertia frob ell) TT T2 a b w := by
  classical
  let F := alpogeNativeFrobInertiaGPsi inertia frob ell
  have heq : ∀ (u : A0) t, t ∈ TT → ∀ j : Fin m,
      (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j) -
        alpogeNativeMAIN ell (a t) (w u j)).re =
      (alpogeNativeFrozenThick F T2 b (a t / b) u t).re +
        (alpogeNativeProjectionWidthReturn F T2 (a t) b u t (w u j) +
          alpogeNativeProjectionThinReturn F T2 (a t) u t (w u j)).re := by
    intro u t ht j
    rw [alpogeNativeFullASK_sub_MAIN_eq_De inertia frob ell N (a t) t (w u j)
      (ha t ht) (hw u j) (hN u j t ht),
      ← alpogeNativeProjectionFullSource_eq_nativeDe inertia frob ell]
    change (alpogeNativeProjectionFullSource F (a t) t (w u j)).re = _
    rw [alpogeNativeProjectionFull_eq_frozen_add_returns F T2 (a t) b u t (w u j),
      Complex.add_re]
  have hsum : (∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
      (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j) -
        alpogeNativeMAIN ell (a t) (w u j)).re) =
      (∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m,
        (alpogeNativeFrozenThick F T2 b (a t / b) u t).re) +
      ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
        (alpogeNativeProjectionWidthReturn F T2 (a t) b u t (w u j) +
          alpogeNativeProjectionThinReturn F T2 (a t) u t (w u j)).re := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => heq u t ht j)
  unfold alpogeNativePhysicalSubgroupTopExcess
  rw [hsum, mul_add,
    alpogeNativeFrozenThick_average_eq_signal A0 F TT T2 hTT hT2 m a b]
  rfl

/-- The finite paid character/source inequality.  There is no analytic
upper-bound hypothesis: the RHS is the complete original physical ASK.
It can be consumed by a genuine geometric bound on that same witness. -/
theorem alpogeNativePhysicalSubgroup_pays_retained
    (A0 : AddSubgroup H)
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT T2 : Finset H) (hTT : TT.Nonempty)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (a : H → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (Kp : Finset (AddChar (AlpogeNativeE0 × H) ℂ))
    (hKp : Kp ⊆ alpogeNativeProjectionChars A0)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ)) :
    alpogeNativeProjectionDivisor TT T2 m b *
      (alpogeNativeRetainedSignal (alpogeNativeFrobInertiaGPsi inertia frob ell) Kp TT a b -
        alpogeNativeExcludedCharacterMass A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
          Kp TT a b) +
      alpogeNativeProjectionSignedRemainder A0
        (alpogeNativeFrobInertiaGPsi inertia frob ell) TT T2 a b w ≤
      alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w := by
  rw [alpogeNativePhysicalSubgroup_eq_projected_add_remainder
    A0 inertia frob ell N TT T2 hTT hT2 a b w ha hw hN]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left
  · exact alpogeNativeRetained_sub_excluded_le_projected A0
      (alpogeNativeFrobInertiaGPsi inertia frob ell) Kp hKp TT a b
  · unfold alpogeNativeProjectionDivisor alpogeNativeProjectionDensity
    positivity

end PhysicalAttachment

end RHLean.Analysis

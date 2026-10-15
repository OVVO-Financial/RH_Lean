import «research.MERTENS_AMPLITUDE_STRIP_MAP»

/-!
# Literal complex-strip realization of an amplitude band

The supplied height t is free; the amplitude determines only the real part.
This gives a coordinate map into an actual complex vertical strip. It makes
no assertion that any of these constructed points is a zeta zero.
-/

noncomputable section
namespace RHLean.Analysis.MertensAmplitude
open Set

/-- A literal complex point whose horizontal coordinate encodes amplitude. -/
def amplitudeStripPoint (x A t : ℝ) : ℂ := ⟨amplitudeCoordinate x A, t⟩

/-- The closed vertical strip with real-part endpoints l and u. -/
def amplitudeVerticalStrip (l u : ℝ) : Set ℂ := {z | z.re ∈ Set.Icc l u}

/-- Actual complex-strip membership is exactly amplitude-band membership. -/
theorem stripPoint_mem_iff {x A l u : ℝ} (hx : 1 < x) (hA : 0 < A) (t : ℝ) :
    amplitudeStripPoint x A t ∈ amplitudeVerticalStrip l u ↔
      A ∈ amplitudeBand x l u := coordinate_mem_Icc_iff hx hA

/-- At every height, amplitude reflection is reflection in the critical line. -/
theorem stripPoint_reflection {x A : ℝ} (hx : 1 < x) (hA : 0 < A) (t : ℝ) :
    amplitudeStripPoint x (reflectedAmplitude x A) t =
      1 - star (amplitudeStripPoint x A t) := by
  apply Complex.ext
  · change amplitudeCoordinate x (reflectedAmplitude x A) = 1 - amplitudeCoordinate x A
    exact coordinate_reflection hx hA
  · change t = 0 - (-t)
    ring

/-- Letting the independent height vary maps the entire amplitude band onto
the entire complex strip, with no claim about the subset of zeta zeros. -/
theorem image_amplitudeBand_all_heights {x : ℝ} (hx : 1 < x) (l u : ℝ) :
    (fun p : ℝ × ℝ => amplitudeStripPoint x p.1 p.2) ''
      (amplitudeBand x l u ×ˢ (Set.univ : Set ℝ)) = amplitudeVerticalStrip l u := by
  ext z
  constructor
  · rintro ⟨⟨A, t⟩, hp, rfl⟩
    have hApos : 0 < A :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans hx) l).trans_le hp.1.1
    exact (stripPoint_mem_iff hx hApos t).mpr hp.1
  · intro hz
    refine ⟨(x ^ z.re, z.im), ⟨?_, Set.mem_univ _⟩, ?_⟩
    · apply (coordinate_mem_Icc_iff hx (Real.rpow_pos_of_pos (zero_lt_one.trans hx) z.re)).mp
      rwa [coordinate_rpow hx z.re]
    · apply Complex.ext
      · exact coordinate_rpow hx z.re
      · rfl

/-- Domain-checked complex point for an actual Mertens sample. -/
def mertensStripPoint (n : ℕ) (t : ℝ) : Option ℂ :=
  (mertensAmplitudeCoordinate n).map (fun s => (⟨s, t⟩ : ℂ))

theorem mertensStripPoint_some {n : ℕ} (hn : 2 ≤ n)
    (hM : mertensSummatory n ≠ 0) (t : ℝ) :
    mertensStripPoint n t = some (amplitudeStripPoint (n : ℝ) (mertensAmplitude n) t) := by
  simp only [mertensStripPoint, mertensCoordinate_some hn hM, Option.map_some, amplitudeStripPoint]

theorem mertensStripPoint_none_of_zero {n : ℕ} (hM : mertensSummatory n = 0) (t : ℝ) :
    mertensStripPoint n t = none := by
  simp only [mertensStripPoint, mertensCoordinate_none_of_zero hM, Option.map_none]

end RHLean.Analysis.MertensAmplitude

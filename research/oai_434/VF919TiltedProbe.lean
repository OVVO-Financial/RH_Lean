import «research.oai_434.VF919TiltedLowPhysical»
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData

/-! The single actual normalized probe used by both sides of the tilted argument. -/

namespace OAI
noncomputable section
open scoped Classical ContDiff BigOperators
open Filter Asymptotics
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual RHLeanFiniteSlotGap
local notation "O" => HeckeFamily.O

def tiltedPhysicalExponents (tilt : ℝ) (htilt : 0≤tilt) (htilt1 : tilt<1/960) :
    LowPhysicalExponents where
  x := 17/48-24*tilt
  y := 23/48+12*tilt
  sum_lo := by linarith
  sum_hi := by linarith
  x_gt_slot := by linarith
  x_lt_y := by linarith
  gram_gap := by linarith
  y_le_one := by linarith

def normalizedProbe_tilted (tilt : ℝ) {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ))

def SourceData.tiltedProbe {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : SourceData D) (tilt : ℝ) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  normalizedProbe_tilted tilt F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=>F.w) F.W F.W η

theorem SourceData.tiltedProbe_low {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : SourceData D) (tilt : ℝ) (htilt : 0≤tilt) (htilt1 : tilt<1/960)
    (hcharge : 24*tilt≤(7/8:ℝ)*D.rmin)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.tiltedProbe tilt η=O[atTop](fun Z : ℝ=>Z^(3/16-9*tilt+loss)) := by
  let phys := tiltedPhysicalExponents tilt htilt htilt1
  have hgap (i : Fin D.N) : (5/3:ℝ)-2*(phys.x+phys.y)≤D.ell i := by
    have hi := (D.slots_bounds i).2.1
    dsimp [phys,tiltedPhysicalExponents]
    linarith
  obtain ⟨C,hC,hb⟩ := original_normalized_compensatedPhysicalProbe_low_tilted phys
    F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j=>(D.slots_bounds j).1)
    D.slots_injective D.slots_sum hgap
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨C,hC,hb.mono ?_⟩
  intro Z hZ
  have he : (5*phys.x+phys.y)/12=3/16-9*tilt := by
    dsimp [phys,tiltedPhysicalExponents]
    ring
  have hh := hZ.2
  rw [he] at hh
  simpa only [SourceData.tiltedProbe,normalizedProbe_tilted,phys,
    tiltedPhysicalExponents] using hh

/-- A positive tilt fixed from the source data before the character and the loss. -/
theorem SourceData.fixed_tiltedProbe_low {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : SourceData D) (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.tiltedProbe (D.e/48) η=O[atTop](fun Z : ℝ=>Z^(3/16-9*(D.e/48)+loss)) := by
  obtain ⟨hd,hcharge,hd1,_⟩ := source_gain_budgets D
  exact F.tiltedProbe_low (D.e/48) hd.le hd1 hcharge.le loss hloss η

#print axioms SourceData.fixed_tiltedProbe_low
end SevenEighths.ProbeFinalAssembly
end
end OAI

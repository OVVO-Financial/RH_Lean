import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile

/-!
# Seven-eighths by the actual LOW/HIGH common-probe mechanism

The intermediate analytic estimates are the pinned, proved OpenAI estimates.
The certificate instantiation, common-probe assembly, and supremum contradiction
are written here, rather than supplied by an imported terminal nonvanishing
result. In particular this file does not import FinalAssemblyUnconditional.

The proof keeps the same actual Hecke family, selected-prime slots, source
exclusions, window-dependent principal normalizer, and signal on both sides.
The assumption beta > 7/8 is introduced only inside a contradiction and is
DISCHARGED. No moment inequality or zero-free conclusion is an extra premise.

This is a local assembly of the existing analytic mechanism, not a new proof
of the imported theta/Poisson and moment estimates on arbitrary sharp windows.
The downstream Mertens/covariance consequences may use the existing converse;
a direct sharp covariance proof without this intermediate remains separate.

Upstream source: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

namespace RHLean.Analysis.VF919SevenEighths

open OAI OAI.SevenEighths
open Filter Asymptotics
open HeckeFamily HeckeZeroSupremum
open ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentEnergyCertifiedExistence
open CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile

/-- Instantiate the proved intermediate band certificate on the actual
source. This proves the analytic input instead of postulating it. -/
theorem certifiedBands : DetectorCertifiedBands := by
  intro hβ D _hfine F bΦ hbΦ
  have hp := fixed_parameters D
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
    (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1.le
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

/-- The inverse, marked-plain, and unmarked-plain moment inputs are
assembled by their proved source_moments theorem at admissible fine slots. -/
theorem chosenMoments : ChosenMomentInput :=
  chosen_input_of_fine (fine_moments_of_certified certifiedBands)

/-- LOW and HIGH refer to exactly the same normalized physical probe.
This spells out the assembly rather than calling the upstream common-probe
or nonvanishing wrapper. Polynomial height losses are absorbed by the
proved choice of tau before the two estimates are combined. -/
theorem commonProbe : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  obtain ⟨D, F, counts, J, hJ, hmom⟩ := chosenMoments hβ
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, hsource⟩ :=
    chosen_data_height D F counts J hJ hmom
  obtain ⟨C, hC, hhigh⟩ :=
    fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta - 7/8) / 2
  have hloss : 0 < loss := by dsimp [loss]; linarith
  have hlossgap : loss < HeckeZeroSupremum.beta - 7/8 := by
    dsimp [loss]
    linarith
  refine ⟨loss, D.sigma, hloss, hlossgap, D.sigma_pos, ?_⟩
  intro η _hprimitive
  obtain ⟨hmask, hH, hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,
    sourceCorrection η F.S, F.probe η,
    hmask, hH, hHbound, F.probe_low loss hloss η, ?_⟩
  obtain ⟨Ct, hCt, hhigh⟩ := hhigh η
  obtain ⟨Cm, hCm, hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct + C * Cm * (η.modulus.absNorm : ℝ) ^ (2 * D.eps),
    by positivity, ?_⟩
  filter_upwards [hhigh, hsource] with Z hh hs
  exact hh Cm hCm.le hs

/-- A zero arbitrarily near the actual supremum contradicts the improved
signal exponent. The Gaussian is retained in the Mellin product identity;
there is no inverse-Gaussian norm estimate or sharp-cutoff premise here. -/
theorem beta_le_seven_eighths : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) := by
  by_contra hn
  obtain ⟨omegaLoss, σ, hω0, hω, hσ, hcontract⟩ := commonProbe (lt_of_not_ge hn)
  have hmargin := Supremum.continuationMargin_pos hω hσ
  have hboundary := Supremum.continuation_boundary_gt (β := beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc =>
        hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole, hz, zero_mul]
  apply (HeckeSignal.nonzero_of_probe_bounds χ H J beta omegaLoss σ (-11/16)
    beta_le_one hω0 hω hσ hH hb ?_ ?_ hnear hχpole) hzχ
  · convert hJ using 1; ring_nf
  · convert herr using 1; ring_nf

/-- All actual Hecke characters, with the principal pole exception explicit.
No hBeta, hMoment, or imported terminal zero-free theorem is supplied. -/
theorem hecke_nonzero (χ : Character) (s : ℂ)
    (hs : (7/8 : ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ (beta_le_seven_eighths.trans_lt hs) hpole

/-- Rational Dirichlet characters obtained from the proved Hecke conclusion. -/
theorem dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  exact HeckeDirichlet.dirichlet_seven_eighths_of_hecke hecke_nonzero χ s hs hexc

/-- The unconditional seven-eighths conclusion derived by this module's
certified moments -> LOW/HIGH -> Mellin contradiction chain. -/
theorem zeta_nonzero (s : ℂ) (hs : (7/8 : ℝ) < s.re) :
    riemannZeta s ≠ 0 :=
  HeckeDirichlet.zeta_seven_eighths_of_hecke hecke_nonzero s hs

#print axioms certifiedBands
#print axioms chosenMoments
#print axioms commonProbe
#print axioms beta_le_seven_eighths
#print axioms hecke_nonzero
#print axioms dirichlet_nonzero
#print axioms zeta_nonzero

end RHLean.Analysis.VF919SevenEighths

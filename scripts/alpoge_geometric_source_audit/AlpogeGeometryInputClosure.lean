import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolGeOfHilbertSamuel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelOfPrincipalisation
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationClosed
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.CycleHeightFormulas.CycleHeightsDirect
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.PoincareLelongInv
import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.AbelianDeRhamDuality
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTer
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesAut
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.HarishChandraModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodChernWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrincipalPolarisationUniqueSection
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers
import Development.AutomorphicArithmetic.ThetaCorrespondence.PrismaticDieudonne.PrismaticDieudonneHodge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegOfNadelVanishingPair
import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopNSI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.Development
import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormHyperplaneSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalIntegralHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeBis

/-!
# Closed geometric input assembly, checked from pinned source

This audit target assembles the six universal input packages of the actual
short-section constructor.  It deliberately does not import an every-character
or RH assembly.  Every field below is the concrete supplying expression found
at upstream commit 7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.

This file is an upstream-source verification target, not a claim that its
dependency closure has already been ported to RH_Lean's Mathlib version.
Its fresh hosted build and axiom/declaration audit are separate acceptance
steps.  No mathematical hypothesis is replaced by a structure assumption.
-/

set_option autoImplicit false

namespace RHLean.UpstreamGeometryAudit

theorem grothendieckDeformation : GlobalTheory.Published.GrothendieckDeformation :=
  GlobalTheory.Published.grothendieckDeformation_of_lifting
    PositivityTheory.DualRT.abelianDeRham
    GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers

theorem hodgeBundleTheorems : GlobalTheory.CovTop.PublishedHodgeBundleTheorems where
  p1 := GlobalTheory.toroidalCompactification_holds
  p2 := GlobalTheory.VolBr.volGe_of_hilbertSamuel
    (GlobalTheory.arithHilbertSamuel_of_principalisation
      PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed)
    (GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct
      PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK)
    GlobalTheory.nefNumerics_outright
  p3 := GlobalTheory.Published.ArithHilbertSamuel.volNef
    (GlobalTheory.arithHilbertSamuel_of_principalisation
      PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed)
  p4 := GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct
    PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK
  p5 := PositivityTheory.DualRT.abelianDeRham
  p8 := PositivityTheory.Stage1.PM.rayClassFieldSt
  p12 := GlobalTheory.SS.semistableReductionSt
  p13 := GlobalTheory.StrongApproxSUProof.strongApproxSU
  p14 := PositivityTheory.Prw.greenSeriesSt_of PositivityTheory.Stage1.PM.greenCuspidal
  p16 := GlobalTheory.GoodMetric.goodChernWeil
  p19 := (GlobalTheory.QNorm.landherr_and_landherrSt).2
  p20 := GlobalTheory.QNorm.hasseNormSt
  p22 := GlobalTheory.semiAbelianHomExtension_holds
  p23 := GlobalTheory.Alc.inducedSimpleLowestAlcove
  p25 := GlobalTheory.AbLaw.principalPolarisation_unique_section
  p26 := GlobalTheory.abMulN_holds
  q1 := GlobalTheory.Published.GrothendieckDeformation.grothendieckMessing
    grothendieckDeformation
  q4 := UpperTheory.Lit.prismaticDieudonneHodge
  q6 := GlobalTheory.KVFromPair.kawamataViehweg_of_nadelVanishingPair
    GlobalTheory.nefNumerics_outright
    (NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor).1
  q7 := GlobalTheory.nefNumerics_outright
  q8 := GlobalTheory.l2ExtensionLogCanonical'
  q9 := GlobalTheory.arithHilbertSamuel_of_principalisation
    PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed
  q10 := GlobalTheory.Published.chowFormExists_holds
  q11 := GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct
    PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK
  q13 := GlobalTheory.Published.serreHolomorphicSections_holds
  q15 := NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor
  q16 := PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed
  q18 := PositivityTheory.FormalThickening.formalAlgebraisation

theorem hsQuoted : GlobalTheory.HSCore.Quoted where
  kv := hodgeBundleTheorems.q6
  l2 := hodgeBundleTheorems.q8
  gaga := hodgeBundleTheorems.q13
  nef := hodgeBundleTheorems.q7
  chow := hodgeBundleTheorems.q10
  chowInt := GlobalTheory.Published.chowFormIntExists_holds
  chowCut := ChowFormCompatibility.chow_form_hyperplane_section
  len := GlobalTheory.Published.ProperIntersectionLength_holds

theorem siegelToroidalIntegral : GlobalTheory.Published.SiegelToroidalIntegral :=
  GlobalTheory.siegelToroidalIntegral_holds

theorem toroidalForFanKS : GlobalTheory.Published.ToroidalForFanKS :=
  GlobalTheory.TorKSField.toroidalForFanKS

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative :=
  GlobalTheory.Nef.semiAbelianLieSeminegative

end RHLean.UpstreamGeometryAudit

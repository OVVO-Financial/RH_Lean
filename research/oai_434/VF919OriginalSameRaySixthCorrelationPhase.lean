import OAI.NumberTheory.DirichletL.Detector.PrimePhase
import OAI.NumberTheory.DirichletL.Detector.LowRay
import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation

/-!
# Original exceptional same-ray coprime sextic correlation is COHERENT

For coprime primary good Eisenstein prime moduli u,v in the same
physical ray modulo 4, the CRT local-correlation phase at any
sixth-power frequency is exactly +1. The proof uses the ORIGINAL
support-opposite-phase reciprocity and actual prime self-sign identity,
not independence or numerical heuristics.

This file only certifies the *phase* identity. Transporting it to the
fully weighted actualCorrelation and the original signed
SourceCanonicalSum is a distinct analytical obligation.
-/

namespace OAI
noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ActualEisensteinCoordinates
open ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CompletedGauss CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open SevenEighths.ProbePhase
local notation "O" => ActualEisensteinCubic.O

theorem original_coprime_same_ray_sextic_correlation_phase_one
    (u v : O)
    (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v}))
    (hpu : goodLambda ^ 2 ∣ u - 1)
    (hpv : goodLambda ^ 2 ∣ v - 1)
    (hcop : IsCoprime u v)
    [Fintype (O ⧸ Ideal.span {u})]
    [(Ideal.span {v} : Ideal O).IsMaximal]
    (hgood : goodLambda ∉ Ideal.span {v})
    (hchar : ringChar (O ⧸ Ideal.span {v}) ≠ 2)
    (hray : physicalRay u = physicalRay v) :
    idealRowHom (-u) (Ideal.span {v}) *
      star (idealRowHom v (Ideal.span {u})) = 1 := by
  have hdiff : (4 : O) ∣ u - v := by
    change (Ideal.Quotient.mk (Ideal.span {(4 : O)}) u) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) v at hray
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hray)
  have hres : residue u = residue v :=
    QuadraticGaussRay.residue_eq_of_four_dvd_sub u v hdiff
  have hphase : sexticReciprocityPhase u v =
      sexticReciprocityPhase v v := by
    unfold sexticReciprocityPhase
    rw [hres]
  have hself := reciprocitySign_self_eq_sextic_neg_one v
    (supported_element_ne_zero v hv) hgood hchar
    (supported_residue_odd v hv)
  have hminus : idealRowHom (-1) (Ideal.span {v}) =
      sexticReciprocityPhase v v := by
    rw [idealRowHom_prime (-1) (Ideal.span {v}) hgood]
    exact hself.symm
  have hcross := supported_opposite_phase u v hu hv hpu hpv hcop
  rw [show -u = (-1) * u by ring, idealRowHom_argument_mul]
  calc
    idealRowHom (-1) (Ideal.span {v}) *
        idealRowHom u (Ideal.span {v}) *
          star (idealRowHom v (Ideal.span {u})) =
      idealRowHom (-1) (Ideal.span {v}) *
        (idealRowHom u (Ideal.span {v}) *
          star (idealRowHom v (Ideal.span {u}))) := by ring
    _ = sexticReciprocityPhase v v * sexticReciprocityPhase u v := by
      rw [hminus, hcross]
    _ = sexticReciprocityPhase v v ^ 2 := by rw [hphase]; ring
    _ = 1 := by
      change (reciprocitySign v v) ^ 2 = 1
      exact reciprocitySign_sq v v (supported_residue_odd v hv)
        (supported_residue_odd v hv)

#print axioms original_coprime_same_ray_sextic_correlation_phase_one

end SevenEighths.ProbePhysical
end
end OAI
